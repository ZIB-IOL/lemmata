module

public import Lemmata.SpanningTreeMinSplit.Main
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

namespace Lemmata.SpanningTreeCommonInformation

open Lemmata.SpanningTreeMinSplit
open scoped BigOperators Classical
noncomputable section

/-- Finiteness follows from the finite ambient graph type, not a tree-count formula. -/
instance treeFintype (n : ℕ) : Fintype (Tree n) := Fintype.ofFinite _

/-- The labelled path is an actual tree whenever there is a vertex. -/
instance treeNonempty (n : ℕ) [NeZero n] : Nonempty (Tree n) :=
  ⟨⟨SimpleGraph.pathGraph n, SimpleGraph.isTree_pathGraph.mpr (NeZero.ne n)⟩⟩

/-- Separate the empty, singleton, full and proper nonsingleton subsets. -/
theorem sum_subsets_partition {n : ℕ} (hn : 2 ≤ n) (f : Finset (Fin n) → ℝ) :
    ∑ S, f S = f ∅ + (∑ v : Fin n, f {v}) + f Finset.univ +
      ∑ S : Subtour n, f S.val := by
  let p := fun S : Finset (Fin n) => 2 ≤ S.card ∧ S.card < n
  have hbad : Finset.univ.filter (fun S => ¬ p S) =
      insert ∅ (insert Finset.univ (Finset.univ.image (fun v : Fin n => ({v} : Finset (Fin n))))) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_image, p]
    have hle : S.card ≤ n := by simpa using S.card_le_univ
    constructor
    · intro h
      by_cases h0 : S.card = 0
      · exact Or.inl (Finset.card_eq_zero.mp h0)
      by_cases h1 : S.card = 1
      · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h1
        exact Or.inr (Or.inr ⟨v, rfl⟩)
      · exact Or.inr (Or.inl ((Finset.card_eq_iff_eq_univ S).mp (by simp; omega)))
    · rintro (rfl | rfl | ⟨v, rfl⟩) <;> simp
  have hfull : (Finset.univ : Finset (Fin n)) ∉
      Finset.univ.image (fun v : Fin n => ({v} : Finset (Fin n))) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro v h
    have := congrArg Finset.card h
    simp at this
    omega
  have hempty : (∅ : Finset (Fin n)) ∉
      insert Finset.univ (Finset.univ.image (fun v : Fin n => ({v} : Finset (Fin n)))) := by
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or, not_exists]
    constructor
    · intro h
      have := congrArg Finset.card h
      simp at this
      omega
    · intro v h
      simpa using congrArg Finset.card h
  have hgood := Finset.sum_subtype (p := p) (F := inferInstance) (Finset.univ.filter p) (by simp) f
  have h := Finset.sum_filter_add_sum_filter_not Finset.univ p f
  rw [hbad, Finset.sum_insert hempty, Finset.sum_insert hfull,
    Finset.sum_image (by intro a _ b _ h; simpa using h), hgood] at h
  change (∑ S : Subtour n, f S.val) + _ = _ at h
  linarith

/-- Exact number of proper nonsingleton rows, in an additive form without
truncated subtraction. -/
theorem card_subtour_add (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (Subtour n) + n + 2 = 2 ^ n := by
  have h := sum_subsets_partition hn (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_finset, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at h
  exact_mod_cast (show (Fintype.card (Subtour n) : ℝ) + n + 2 = 2 ^ n by linarith)

/-- The subtour row count. -/
theorem card_subtour (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (Subtour n) = 2 ^ n - n - 2 := by
  have := card_subtour_add n hn
  omega

/-- Increasing endpoint pairs enumerate the unordered edges exactly once. -/
theorem card_edge (n : ℕ) : Fintype.card (Edge n) = n * (n - 1) / 2 := by
  let e : Edge n ≃ Σ b : Fin n, {a : Fin n // a < b} :=
    { toFun := fun e => ⟨e.val.2, ⟨e.val.1, e.property⟩⟩
      invFun := fun e => ⟨(e.2.val, e.1), e.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  have h (b : Fin n) : Fintype.card {a : Fin n // a < b} = b.val := by
    rw [Fintype.card_subtype]
    have : Finset.univ.filter (fun a : Fin n => a < b) = Finset.Iio b := by ext; simp
    rw [this, Fin.card_Iio]
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => k), Finset.sum_range_id]

/-- Count both kinds of rows in the published full matrix. -/
theorem card_row (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (Row n) = (2 ^ n - n - 2) + n * (n - 1) / 2 := by
  rw [Fintype.card_sum, card_subtour n hn, card_edge]

/-- Subtour row count with all subtractions performed in the reals. -/
theorem card_subtour_real (n : ℕ) (hn : 2 ≤ n) :
    (Fintype.card (Subtour n) : ℝ) = (2 : ℝ) ^ n - (n : ℝ) - 2 := by
  have h : (Fintype.card (Subtour n) : ℝ) + n + 2 = 2 ^ n := by
    exact_mod_cast card_subtour_add n hn
  linarith

/-- Real form of the edge count, with exact division by two. -/
theorem card_edge_real (n : ℕ) (hn : 1 ≤ n) :
    (Fintype.card (Edge n) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  have h : 2 * Fintype.card (Edge n) = n * (n - 1) := by
    rw [card_edge, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
  have hreal : (2 : ℝ) * Fintype.card (Edge n) = (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [Nat.cast_sub hn, Nat.cast_one] at hreal
  linarith

/-- Real form of the total row count. -/
theorem card_row_real (n : ℕ) (hn : 2 ≤ n) :
    (Fintype.card (Row n) : ℝ) =
      (2 : ℝ) ^ n - (n : ℝ) - 2 + (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  rw [Fintype.card_sum, Nat.cast_add, card_subtour_real n hn, card_edge_real n (by omega)]

/-- The published factor count in real arithmetic; no slots are added. -/
theorem card_cert_real (n : ℕ) (hn : 1 ≤ n) :
    (Fintype.card (Cert n) : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  have h : (6 : ℝ) * Fintype.card (Cert n) =
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) * ((2 * n - 1 : ℕ) : ℝ) := by
    exact_mod_cast six_mul_card_cert n
  rw [Nat.cast_sub hn, Nat.cast_sub (show 1 ≤ 2 * n by omega)] at h
  push_cast at h
  linarith

/-- Number of all subsets containing a prescribed vertex set. -/
theorem card_supersets {n : ℕ} (A : Finset (Fin n)) :
    (Finset.univ.filter (fun S : Finset (Fin n) => A ⊆ S)).card = 2 ^ (n - A.card) := by
  have h : (Finset.univ.filter (fun S : Finset (Fin n) => A ⊆ S)).card =
      ((Finset.univ \ A).powerset).card := by
    symm
    apply Finset.card_bij (fun B _ => A ∪ B)
    · intro B hB
      simp
    · intro B hB C hC h
      have hB := Finset.mem_powerset.mp hB
      have hC := Finset.mem_powerset.mp hC
      ext v
      have hv := Finset.ext_iff.mp h v
      by_cases ha : v ∈ A
      · have hb : v ∉ B := fun h => (Finset.mem_sdiff.mp (hB h)).2 ha
        have hc : v ∉ C := fun h => (Finset.mem_sdiff.mp (hC h)).2 ha
        simp [hb, hc]
      · simpa [ha] using hv
    · intro S hS
      have hAS := (Finset.mem_filter.mp hS).2
      refine ⟨S \ A, Finset.mem_powerset.mpr ?_, ?_⟩
      · exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _)
      · exact Finset.union_sdiff_of_subset hAS
  rw [h, Finset.card_powerset, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

/-- The real-valued indicator sum for containing any prescribed subset. -/
theorem sum_supersets {n : ℕ} (A : Finset (Fin n)) :
    (∑ S : Finset (Fin n), if A ⊆ S then (1 : ℝ) else 0) = 2 ^ (n - A.card) := by
  rw [Finset.sum_boole, card_supersets]
  simp

/-- Double count vertex/subset incidences. -/
theorem sum_card_subsets (n : ℕ) :
    (∑ S : Finset (Fin n), (S.card : ℝ)) = (n : ℝ) * 2 ^ (n - 1) := by
  have h (S : Finset (Fin n)) : (S.card : ℝ) =
      ∑ v : Fin n, if ({v} : Finset (Fin n)) ⊆ S then (1 : ℝ) else 0 := by
    simp
  simp_rw [h]
  rw [Finset.sum_comm]
  simp_rw [sum_supersets, Finset.card_singleton]
  simp

/-- Internal tree edges reindexed by the fixed-root child bijection, with
membership expressed on both endpoints. The subset need not contain the root. -/
theorem internal_edges_eq_child_indicators {n : ℕ} (T : Tree n) (r : Fin n)
    (S : Finset (Fin n)) :
    (∑ e ∈ S.sym2, edgeValue T e) =
      ∑ v : Child r, if ({v.val, parent T r v.val} : Finset (Fin n)) ⊆ S
        then (1 : ℝ) else 0 := by
  rw [internal_edges_eq_parents T S r]
  calc
    _ = ∑ v ∈ S.erase r, if ({v, parent T r v} : Finset (Fin n)) ⊆ S
          then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [Finset.insert_subset_iff, (Finset.mem_erase.mp hv).2]
    _ = ∑ v ∈ Finset.univ.erase r, if ({v, parent T r v} : Finset (Fin n)) ⊆ S
          then (1 : ℝ) else 0 := by
      apply Finset.sum_subset (Finset.erase_subset_erase r (Finset.subset_univ S))
      intro v hv hvs
      have hvne := (Finset.mem_erase.mp hv).1
      have hvS : v ∉ S := fun h => hvs (Finset.mem_erase.mpr ⟨hvne, h⟩)
      simp [Finset.insert_subset_iff, hvS]
    _ = _ := Finset.sum_subtype (F := inferInstance) _ (by simp) _

/-- Each of the n-1 genuine tree edges occurs in 2^(n-2) subsets. -/
theorem sum_internal_edges {n : ℕ} (T : Tree n) (hn : 2 ≤ n) :
    (∑ S : Finset (Fin n), ∑ e ∈ S.sym2, edgeValue T e) =
      ((n : ℝ) - 1) * 2 ^ (n - 2) := by
  let r : Fin n := ⟨0, by omega⟩
  simp_rw [internal_edges_eq_child_indicators T r]
  rw [Finset.sum_comm]
  have hpair (v : Child r) : ({v.val, parent T r v.val} : Finset (Fin n)).card = 2 := by
    simp [Ne.symm (parent_ne_self T r v.val v.property)]
  simp_rw [sum_supersets, hpair]
  have hcard : Fintype.card (Child r) = n - 1 := by
    simp [Child, Fintype.card_subtype_compl]
  simp [hcard, Nat.cast_sub (show 1 ≤ n by omega)]

/-- Recover the explicit slack formula from the published public counting
lemmas. This avoids requiring the older module's unexposed definition body. -/
theorem subtourSlack_formula {n : ℕ} (T : Tree n) (S : Finset (Fin n))
    (hS : S.Nonempty) :
    subtourSlack T S = (S.card : ℝ) - 1 - ∑ e ∈ S.sym2, edgeValue T e := by
  obtain ⟨r, hr⟩ := hS
  have hcard : ((S.erase r).card : ℝ) = (S.card : ℝ) - 1 := by
    have h : ((S.erase r).card : ℝ) + 1 = (S.card : ℝ) := by
      exact_mod_cast Finset.card_erase_add_one hr
    linarith
  have hsplit :
      (∑ v ∈ S.erase r, if parent T r v ∈ S then (1 : ℝ) else 0) +
      (∑ v ∈ S.erase r, if parent T r v ∉ S then (1 : ℝ) else 0) =
      ((S.erase r).card : ℝ) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _v ∈ S.erase r, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases h : parent T r v ∈ S <;> simp [h]
      _ = _ := by simp
  rw [subtourSlack_eq_splits T S r hr, internal_edges_eq_parents T S r]
  linarith

/-- Singleton subsets have zero slack in every actual simple tree. -/
theorem subtourSlack_singleton {n : ℕ} (T : Tree n) (v : Fin n) :
    subtourSlack T {v} = 0 := by
  rw [subtourSlack_eq_splits T {v} v (Finset.mem_singleton_self v)]
  simp

/-- The full vertex set has zero subtour slack. -/
theorem subtourSlack_univ {n : ℕ} (T : Tree n) (hn : 0 < n) :
    subtourSlack T Finset.univ = 0 := by
  let r : Fin n := ⟨0, hn⟩
  rw [subtourSlack_eq_splits T Finset.univ r (Finset.mem_univ r)]
  simp

/-- The mass of the proper subtour rows in every actual tree column. -/
theorem sum_subtourSlack {n : ℕ} (T : Tree n) (hn : 3 ≤ n) :
    (∑ S : Subtour n, subtourSlack T S.val) =
      ((n : ℝ) - 3) * 2 ^ (n - 2) + 1 := by
  let f := fun S : Finset (Fin n) => (S.card : ℝ) - 1 - ∑ e ∈ S.sym2, edgeValue T e
  have htotal : (∑ S : Finset (Fin n), f S) =
      (n : ℝ) * 2 ^ (n - 1) - 2 ^ n - ((n : ℝ) - 1) * 2 ^ (n - 2) := by
    simp only [f, Finset.sum_sub_distrib]
    rw [sum_card_subsets, sum_internal_edges T (by omega)]
    simp
  have hpartition := sum_subsets_partition (n := n) (by omega : 2 ≤ n) f
  have hempty : f ∅ = -1 := by simp [f]
  have hsingle (v : Fin n) : f {v} = 0 :=
    (subtourSlack_formula T {v} (Finset.singleton_nonempty v)).symm.trans
      (subtourSlack_singleton T v)
  have hfull : f Finset.univ = 0 :=
    (subtourSlack_formula T Finset.univ ⟨⟨0, by omega⟩, Finset.mem_univ _⟩).symm.trans
      (subtourSlack_univ T (by omega))
  have hsub : (∑ S : Subtour n, f S.val) = ∑ S : Subtour n, subtourSlack T S.val :=
    Finset.sum_congr rfl (fun S _ => (subtourSlack_formula T S.val (subtour_nonempty S)).symm)
  simp only [hempty, hsingle, hfull, hsub, Finset.sum_const_zero, add_zero] at hpartition
  have hpow1 : (2 : ℝ) ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [show n - 1 = n - 2 + 1 by omega, pow_succ]
    ring
  have hpow2 : (2 : ℝ) ^ n = 4 * 2 ^ (n - 2) := by
    calc
      (2 : ℝ) ^ n = 2 ^ (n - 2 + 2) := congrArg _ (by omega)
      _ = 4 * 2 ^ (n - 2) := by rw [pow_add]; ring
  rw [hpow1, hpow2] at htotal
  nlinarith [htotal, hpartition]

/-- The increasing edge rows pick out exactly the actual edges of the tree. -/
theorem sum_edge_incidence {n : ℕ} (T : Tree n) :
    (∑ e : Edge n, if T.val.Adj e.val.1 e.val.2 then (1 : ℝ) else 0) =
      (n : ℝ) - 1 := by
  have hcard : (Finset.univ.filter (fun e : Edge n => T.val.Adj e.val.1 e.val.2)).card =
      T.val.edgeFinset.card := by
    apply Finset.card_bij (fun e _ => s(e.val.1, e.val.2))
    · intro e he
      exact SimpleGraph.mem_edgeFinset.mpr ((Finset.mem_filter.mp he).2)
    · intro e he f hf h
      rcases Sym2.eq_iff.mp h with h | h
      · exact Subtype.ext (Prod.ext h.1 h.2)
      · have hef : e.val.1 < e.val.2 := e.property
        have hfe : e.val.2 < e.val.1 := by simpa [h.1, h.2] using f.property
        exact (lt_asymm hef hfe).elim
    · intro e
      induction e using Sym2.inductionOn with
      | hf a b =>
        intro he
        have hadj : T.val.Adj a b := SimpleGraph.mem_edgeFinset.mp he
        by_cases hab : a < b
        · exact ⟨⟨(a, b), hab⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩, rfl⟩
        · have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab) hadj.ne.symm
          exact ⟨⟨(b, a), hba⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj.symm⟩,
            Sym2.eq_swap⟩
  rw [Finset.sum_boole, hcard]
  have h : T.val.edgeFinset.card + 1 = n := by simpa using T.property.card_edgeFinset
  have hreal : (T.val.edgeFinset.card : ℝ) + 1 = n := by exact_mod_cast h
  linarith

/-- Every actual full slack column has the same mass: the subtour mass plus
its n-1 genuine tree-edge incidences. -/
theorem sum_fullSlack {n : ℕ} (T : Tree n) (hn : 3 ≤ n) :
    (∑ R : Row n, fullSlack n R T) =
      ((n : ℝ) - 3) * 2 ^ (n - 2) + n := by
  rw [Fintype.sum_sum_type]
  change (∑ S : Subtour n, subtourSlack T S.val) +
    (∑ e : Edge n, if T.val.Adj e.val.1 e.val.2 then (1 : ℝ) else 0) = _
  rw [sum_subtourSlack T hn, sum_edge_incidence T]
  ring

end
end Lemmata.SpanningTreeCommonInformation
