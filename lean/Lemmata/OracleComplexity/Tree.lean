module

public import Lemmata.OracleComplexity.Entropy

@[expose] public section

/-!
# The information lower bound along a query tree

`leafEnt t G` is the scaled entropy of the instance that remains at the leaves of the tree `t` for
the instances in `G`. By the chain rule and the information bound at every query,
`condEnt p G ≤ C ∑_{f ∈ G} p_f T(f) + leafEnt t G`. By Fano's inequality at every leaf and the
superadditivity of the scaled binary entropy, `leafEnt t G` is at most the scaled binary entropy of
the error plus the error times `log(|F| - 1)`. For `G = F` this is Lemma III.1. Emulations map
query trees to query trees with the same outputs and numbers of queries (Lemma III.5).
-/

namespace Lemmata.OracleComplexity

open Real

universe u

variable {F Q A X : Type u}

open Classical in
/-- The scaled entropy of the instance remaining at the leaves of a query tree. -/
noncomputable def leafEnt (p : F → ℝ) (oracle : F → Q → A) : QueryTree Q A X → Finset F → ℝ
  | .ret _, G => condEnt p G
  | .ask q next, G => ∑ a ∈ G.image (fun f => oracle f q),
      leafEnt p oracle (next a) (G.filter (fun f => oracle f q = a))

open Classical in
/-- The information collected by the queries. -/
theorem info_bound (p : F → ℝ) (oracle : F → Q → A) (C : ℝ) (t : QueryTree Q A X) :
    ∀ G : Finset F, InfoBounded p oracle C t G →
      condEnt p G ≤ C * ∑ f ∈ G, p f * (t.queries (oracle f) : ℝ) + leafEnt p oracle t G := by
  induction t with
  | ret x => intro G _; simp [leafEnt, QueryTree.queries]
  | ask q next ih =>
    intro G hG
    obtain ⟨hq, hnext⟩ := hG
    rw [condEnt_chain p oracle q G]
    have hsum : ∑ f ∈ G, p f * ((QueryTree.ask q next).queries (oracle f) : ℝ) =
        weight p G + ∑ a ∈ G.image (fun f => oracle f q),
          ∑ f ∈ G.filter (fun f => oracle f q = a), p f * ((next a).queries (oracle f) : ℝ) := by
      simp only [QueryTree.queries, Nat.cast_add, Nat.cast_one, mul_add, mul_one,
        Finset.sum_add_distrib]
      rw [add_comm]
      unfold weight
      congr 1
      rw [← Finset.sum_fiberwise_of_maps_to (s := G) (t := G.image (fun f => oracle f q))
        (g := fun f => oracle f q) (fun f hf => Finset.mem_image_of_mem _ hf)]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun f hf => ?_
      rw [(Finset.mem_filter.mp hf).2]
    have h1 : ∑ a ∈ G.image (fun f => oracle f q), condEnt p (G.filter (fun f => oracle f q = a))
        ≤ ∑ a ∈ G.image (fun f => oracle f q),
          (C * ∑ f ∈ G.filter (fun f => oracle f q = a), p f * ((next a).queries (oracle f) : ℝ) +
            leafEnt p oracle (next a) (G.filter (fun f => oracle f q = a))) :=
      Finset.sum_le_sum fun a _ => ih a _ (hnext a)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
    have hleaf : leafEnt p oracle (QueryTree.ask q next) G = ∑ a ∈ G.image (fun f => oracle f q),
        leafEnt p oracle (next a) (G.filter (fun f => oracle f q = a)) := by
      simp only [leafEnt]
    rw [hsum, hleaf]
    nlinarith [hq, h1]

open Classical in
/-- Fano's inequality along a query tree. -/
theorem fano_tree [Fintype F] {p : F → ℝ} (hp : ∀ f, 0 ≤ p f) (oracle : F → Q → A)
    (t : QueryTree Q A F) : ∀ G : Finset F,
      leafEnt p oracle t G ≤
        scaledBin (weight p (G.filter (fun f => t.output (oracle f) ≠ f))) (weight p G) +
          weight p (G.filter (fun f => t.output (oracle f) ≠ f)) *
            Real.log ((Fintype.card F : ℝ) - 1) := by
  induction t with
  | ret o =>
    intro G
    simp only [leafEnt, QueryTree.output]
    exact leaf_fano hp G o
  | ask q next ih =>
    intro G
    set img := G.image (fun f => oracle f q) with himg
    set Ga := fun a => G.filter (fun f => oracle f q = a) with hGa
    set err := fun a => weight p ((Ga a).filter (fun f => (next a).output (oracle f) ≠ f))
      with herr_def
    have hleaf : leafEnt p oracle (QueryTree.ask q next) G =
        ∑ a ∈ img, leafEnt p oracle (next a) (Ga a) := by
      simp only [leafEnt, himg, hGa]
    have h1 : ∑ a ∈ img, leafEnt p oracle (next a) (Ga a) ≤
        ∑ a ∈ img, (scaledBin (err a) (weight p (Ga a)) +
          err a * Real.log ((Fintype.card F : ℝ) - 1)) :=
      Finset.sum_le_sum fun a _ => ih a (Ga a)
    rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h1
    have h2 := scaledBin_sum_le img err (fun a => weight p (Ga a))
      (fun a _ => weight_nonneg hp _)
      (fun a _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun f _ _ => hp f))
    have hw : ∑ a ∈ img, weight p (Ga a) = weight p G := by
      unfold weight
      exact Finset.sum_fiberwise_of_maps_to (fun f hf => Finset.mem_image_of_mem _ hf) _
    have herr : ∑ a ∈ img, err a =
        weight p (G.filter (fun f => (QueryTree.ask q next).output (oracle f) ≠ f)) := by
      unfold weight
      simp only [herr_def, hGa, weight]
      rw [← Finset.sum_fiberwise_of_maps_to
        (s := G.filter (fun f => (QueryTree.ask q next).output (oracle f) ≠ f)) (t := img)
        (g := fun f => oracle f q)
        (fun f hf => Finset.mem_image_of_mem _ (Finset.mem_filter.mp hf).1)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.filter_filter, Finset.filter_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      apply Finset.filter_congr
      intro f _
      simp only [QueryTree.output]
      constructor
      · rintro ⟨h1, h2⟩; rw [← h1] at h2; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; rw [h2] at h1; exact ⟨h2, h1⟩
    rw [hw, herr] at h2
    rw [herr] at h1
    rw [hleaf]
    linarith

namespace Proof

theorem info_lower_bound : InfoLowerBound.{u} := by
  intro F Q A _ p oracle C t hp hsum hinfo
  have h1 := info_bound p oracle C t Finset.univ hinfo
  have h2 := fano_tree hp oracle t Finset.univ
  have hw : weight p Finset.univ = 1 := hsum
  have hJ : condEnt p Finset.univ = ∑ f, negMulLog (p f) := by
    simp [condEnt, hw]
  rw [hJ] at h1
  rw [hw] at h2
  have hsb : ∀ e, scaledBin e 1 = binEntropy e := fun e => by
    simp [scaledBin, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [hsb] at h2
  unfold weight at h2
  linarith

/-- The emulation of an algorithm: queries are translated by `qe` and answers back by `ae`. -/
def emulate {Q₁ A₁ Q₂ A₂ : Type u} (qe : Q₁ → Q₂) (ae : Q₁ → A₂ → A₁) :
    QueryTree Q₁ A₁ X → QueryTree Q₂ A₂ X
  | .ret x => .ret x
  | .ask q next => .ask (qe q) (fun b => emulate qe ae (next (ae q b)))

theorem emulation : Emulation.{u} := by
  intro F Q₁ A₁ Q₂ A₂ X oracle₁ oracle₂ qe ae hem t
  refine ⟨emulate qe ae t, fun f => ?_⟩
  induction t with
  | ret x => exact ⟨rfl, rfl⟩
  | ask q next ih =>
    simp only [emulate, QueryTree.output, QueryTree.queries]
    rw [← hem f q]
    exact ⟨(ih _).1, by rw [(ih _).2]⟩

end Proof

end Lemmata.OracleComplexity
