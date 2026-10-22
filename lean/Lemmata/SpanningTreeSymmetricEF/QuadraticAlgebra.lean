module

public import Lemmata.SpanningTreeSymmetricEF.QuadraticTrees
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

@[expose] public section


/-! Affine equations of the exact Gram lift, valid for arbitrary PSD matrices.
The coefficient vectors are fixed data, not additional nonlinear variables. -/
namespace Lemmata.SpanningTreeSymmetricEF.QuadraticAlgebra
open scoped BigOperators
open FormulationStructure
noncomputable section
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

abbrev pair (Y : Matrix J J ℝ) := Matrix.toBilin' Y

def edgesIn (S : Finset V) : Finset (Edge V) :=
  Finset.univ.filter (fun e => ∀ v ∈ e.val, v ∈ S)

@[simp] theorem mem_edgesIn (S : Finset V) (e : Edge V) :
    e ∈ edgesIn S ↔ ∀ v ∈ e.val, v ∈ S := by simp [edgesIn]

structure Equations (active : V → Finset V)
    (a : Edge V → J → ℝ) (b : V → V → J → ℝ)
    (Y : Matrix J J ℝ) (x : Edge V → ℝ) : Prop where
  diagonal : ∀ e, pair Y (a e) (a e) = x e
  edge : ∀ e f, e ≠ f → pair Y (a e) (a f) = 0
  parent : ∀ r v w, pair Y (b r v) (b r w) = if v = w ∧ v ∈ active r then 1 else 0
  incidence : ∀ r v e, v ∉ e.val → pair Y (a e) (b r v) = 0
  conservation : ∀ r e, (∀ v ∈ e.val, v = r ∨ v ∈ active r) →
    (∑ v ∈ active r, pair Y (a e) (b r v)) = x e
  cardinality : ∑ e, x e = (Fintype.card V : ℝ) - 1

theorem pair_symm {Y : Matrix J J ℝ} (hY : Y.PosSemidef) (u v : J → ℝ) :
    pair Y u v = pair Y v u := by
  simp only [pair, Matrix.toBilin'_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h := hY.isHermitian.apply i j
  simp only [star_trivial] at h
  rw [h]
  ring

theorem pair_nonneg {Y : Matrix J J ℝ} (hY : Y.PosSemidef) (u : J → ℝ) :
    0 ≤ pair Y u u := by
  simpa [pair, Matrix.toBilin'_apply'] using hY.dotProduct_mulVec_nonneg u

variable {active : V → Finset V} {a : Edge V → J → ℝ} {b : V → V → J → ℝ}
variable {Y : Matrix J J ℝ} {x : Edge V → ℝ}

/-- The squared norm of the internal-edge sum. -/
theorem Equations.edge_sum (h : Equations active a b Y x) (S : Finset V) :
    pair Y (∑ e ∈ edgesIn S, a e) (∑ e ∈ edgesIn S, a e) = ∑ e ∈ edgesIn S, x e := by
  simp only [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_eq_single e]
  · exact h.diagonal e
  · intro f _ hfe
    exact h.edge e f hfe.symm
  · exact fun hn => (hn he).elim

/-- The squared norm of a root's parent-vector sum. -/
theorem Equations.parent_sum (h : Equations active a b Y x) (S : Finset V) (r : V)
    (hr : r ∈ S) (hroot : r ∉ active r) (hcover : S.erase r ⊆ active r) :
    pair Y (∑ v ∈ S, b r v) (∑ v ∈ S, b r v) = (S.card : ℝ) - 1 := by
  have hf : S.filter (· ∈ active r) = S.erase r := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hv, ha⟩
      exact ⟨fun he => hroot (he ▸ ha), hv⟩
    · rintro ⟨hne,hv⟩
      exact ⟨hv,hcover (Finset.mem_erase.mpr ⟨hne,hv⟩)⟩
  simp only [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  have hi (v : V) (hv : v ∈ S) :
      (∑ w ∈ S, pair Y (b r v) (b r w)) = if v ∈ active r then 1 else 0 := by
    rw [Finset.sum_eq_single v]
    · simp [h.parent]
    · intro w _ hne
      simp [h.parent, hne.symm]
    · exact fun hn => (hn hv).elim
  rw [Finset.sum_congr rfl hi]
  rw [← Finset.sum_filter, hf]
  have hc := Finset.card_erase_add_one hr
  have hc' : ((S.erase r).card : ℝ) + 1 = S.card := by exact_mod_cast hc
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith

/-- Incidence zeros reduce a full-root conservation equation to any subset. -/
theorem Equations.cross_sum (h : Equations active a b Y x)
    (hb : ∀ r v, v ∉ active r → b r v = 0)
    (S : Finset V) (r : V) (hcover : S.erase r ⊆ active r) :
    pair Y (∑ e ∈ edgesIn S, a e) (∑ v ∈ S, b r v) = ∑ e ∈ edgesIn S, x e := by
  simp only [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have heS := (mem_edgesIn S e).mp he
  calc
    _ = ∑ v, pair Y (a e) (b r v) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      exact h.incidence r v e (fun hm => hv (heS v hm))
    _ = ∑ v ∈ active r, pair Y (a e) (b r v) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      simp [hb r v hv]
    _ = x e := h.conservation r e (by
      intro v hv
      by_cases hvr : v = r
      · exact Or.inl hvr
      · exact Or.inr (hcover (Finset.mem_erase.mpr ⟨hvr,heS v hv⟩)))

/-- Every forest slack is a quadratic form in a fixed coefficient vector.
This identity is proved for arbitrary feasible matrices, not just tree witnesses. -/
theorem Equations.forest_identity (h : Equations active a b Y x) (hY : Y.PosSemidef)
    (hb : ∀ r v, v ∉ active r → b r v = 0)
    (S : Finset V) (r : V) (hr : r ∈ S) (hroot : r ∉ active r)
    (hcover : S.erase r ⊆ active r) :
    let u := (∑ v ∈ S, b r v) - ∑ e ∈ edgesIn S, a e
    pair Y u u = (S.card : ℝ) - 1 - ∑ e ∈ edgesIn S, x e := by
  dsimp only
  simp only [map_sub, LinearMap.sub_apply]
  rw [h.parent_sum S r hr hroot hcover, h.edge_sum S,
    pair_symm hY (∑ v ∈ S, b r v) (∑ e ∈ edgesIn S, a e),
    h.cross_sum hb S r hcover]
  ring

theorem Equations.forest_le (h : Equations active a b Y x) (hY : Y.PosSemidef)
    (hb : ∀ r v, v ∉ active r → b r v = 0)
    (S : Finset V) (r : V) (hr : r ∈ S) (hroot : r ∉ active r)
    (hcover : S.erase r ⊆ active r) :
    (∑ e ∈ edgesIn S, x e) ≤ (S.card : ℝ) - 1 := by
  have hn := pair_nonneg hY ((∑ v ∈ S, b r v) - ∑ e ∈ edgesIn S, a e)
  rw [h.forest_identity hY hb S r hr hroot hcover] at hn
  linarith

theorem Equations.nonneg (h : Equations active a b Y x) (hY : Y.PosSemidef) (e : Edge V) :
    0 ≤ x e := by rw [← h.diagonal e]; exact pair_nonneg hY _

end
end Lemmata.SpanningTreeSymmetricEF.QuadraticAlgebra
