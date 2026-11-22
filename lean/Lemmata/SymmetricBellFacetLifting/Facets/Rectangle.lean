module

public import Lemmata.SymmetricBellFacetLifting.Facets.Main
public import Mathlib.Analysis.Convex.Combination

/-! # The projected three-party, four-setting polytope is a rectangle

The two real negacyclic coordinates lie in the indicated rectangle and all
four corners are attained. For the second bound we split the thirty-two terms
into the four odd input parity patterns. At least one block vanishes. -/

@[expose] public section
noncomputable section
open Set Lemmata.SymmetricBellCrossPolytope
namespace Lemmata.SymmetricBellFacetLifting.Facets

private def oddBlock (A A' B B' C C' : ℝ) : ℝ :=
  A*B*C - A'*B*C - A*B'*C - A*B*C' - A'*B'*C - A'*B*C' - A*B'*C' + A'*B'*C'

private def sixSigns (A A' B B' C C' : ℝ) : ℝ := A*A'*B*B'*C*C'

private lemma oddBlock_spec (A A' B B' C C' : ℝ)
    (a : A = 1 ∨ A = -1) (a' : A' = 1 ∨ A' = -1)
    (b : B = 1 ∨ B = -1) (b' : B' = 1 ∨ B' = -1)
    (c : C = 1 ∨ C = -1) (c' : C' = 1 ∨ C' = -1) :
    (-4 ≤ oddBlock A A' B B' C C' ∧ oddBlock A A' B B' C C' ≤ 4) ∧
    (oddBlock A A' B B' C C' ≠ 0 → sixSigns A A' B B' C C' = 1) := by
  rcases a with rfl | rfl <;> rcases a' with rfl | rfl <;>
    rcases b with rfl | rfl <;> rcases b' with rfl | rfl <;>
    rcases c with rfl | rfl <;> rcases c' with rfl | rfl <;> norm_num [oddBlock, sixSigns]

private lemma negSign {x : ℝ} (h : x = 1 ∨ x = -1) : -x = 1 ∨ -x = -1 := by
  rcases h with rfl | rfl <;> norm_num

/-- The odd parity blocks of d₁−d₃ cannot all be nonzero. -/
theorem d13_bounds_atom {v : V} (hv : v ∈ strategySet 3 4) : -12 ≤ d13 v ∧ d13 v ≤ 12 := by
  obtain ⟨a,ha,h⟩ := hv
  have coord (i j k : Fin 4) : v ![i,j,k] = a 0 i * a 1 j * a 2 k := by
    rw [h]; simp [Fin.prod_univ_succ, mul_assoc]
  have square (i : Fin 3) (j : Fin 4) : (a i j)^2 = 1 := by
    rcases ha i j with he | he <;> rw [he] <;> norm_num
  let X := oddBlock (a 0 0) (a 0 2) (a 1 0) (a 1 2) (a 2 1) (a 2 3)
  let pX := sixSigns (a 0 0) (a 0 2) (a 1 0) (a 1 2) (a 2 1) (a 2 3)
  have hX : (-4 ≤ X ∧ X ≤ 4) ∧ (X ≠ 0 → pX = 1) :=
    oddBlock_spec _ _ _ _ _ _ (ha 0 0) (ha 0 2) (ha 1 0) (ha 1 2) (ha 2 1) (ha 2 3)
  let Y := oddBlock (a 0 0) (a 0 2) (a 1 1) (a 1 3) (a 2 0) (a 2 2)
  let pY := sixSigns (a 0 0) (a 0 2) (a 1 1) (a 1 3) (a 2 0) (a 2 2)
  have hY : (-4 ≤ Y ∧ Y ≤ 4) ∧ (Y ≠ 0 → pY = 1) :=
    oddBlock_spec _ _ _ _ _ _ (ha 0 0) (ha 0 2) (ha 1 1) (ha 1 3) (ha 2 0) (ha 2 2)
  let Z := oddBlock (a 0 1) (a 0 3) (a 1 0) (a 1 2) (a 2 0) (a 2 2)
  let pZ := sixSigns (a 0 1) (a 0 3) (a 1 0) (a 1 2) (a 2 0) (a 2 2)
  have hZ : (-4 ≤ Z ∧ Z ≤ 4) ∧ (Z ≠ 0 → pZ = 1) :=
    oddBlock_spec _ _ _ _ _ _ (ha 0 1) (ha 0 3) (ha 1 0) (ha 1 2) (ha 2 0) (ha 2 2)
  let W := oddBlock (-(a 0 3)) (a 0 1) (a 1 1) (a 1 3) (a 2 1) (a 2 3)
  let pW := sixSigns (-(a 0 3)) (a 0 1) (a 1 1) (a 1 3) (a 2 1) (a 2 3)
  have hW : (-4 ≤ W ∧ W ≤ 4) ∧ (W ≠ 0 → pW = 1) :=
    oddBlock_spec _ _ _ _ _ _ (negSign (ha 0 3)) (ha 0 1) (ha 1 1) (ha 1 3) (ha 2 1) (ha 2 3)
  have sum : d13 v = X+Y+Z+W := by
    simp only [d13, add_apply, sub_apply, entry_apply, coord]
    dsimp [X,Y,Z,W,oddBlock]
    ring
  have parities : pX*pY*pZ*pW = -1 := by
    calc
      _ = -((a 0 0)^2*(a 0 1)^2*(a 0 2)^2*(a 0 3)^2*
            (a 1 0)^2*(a 1 1)^2*(a 1 2)^2*(a 1 3)^2*
            (a 2 0)^2*(a 2 1)^2*(a 2 2)^2*(a 2 3)^2) := by
              dsimp [pX,pY,pZ,pW,sixSigns]; ring
      _ = -1 := by simp only [square, mul_one]
  have hz : X = 0 ∨ Y = 0 ∨ Z = 0 ∨ W = 0 := by
    by_contra! hn
    rw [hX.2 hn.1, hY.2 hn.2.1, hZ.2 hn.2.2.1, hW.2 hn.2.2.2] at parities
    norm_num at parities
  rcases hX.1 with ⟨xl,xu⟩
  rcases hY.1 with ⟨yl,yu⟩
  rcases hZ.1 with ⟨zl,zu⟩
  rcases hW.1 with ⟨wl,wu⟩
  rcases hz with h0 | h0 | h0 | h0 <;> constructor <;> linarith

private lemma neg_strategy {v : V} (hv : v ∈ strategySet 3 4) : -v ∈ strategySet 3 4 := by
  obtain ⟨a,ha,h⟩ := hv
  refine ⟨![fun i => -a 0 i, a 1, a 2], ?_, ?_⟩
  · intro n i
    fin_cases n
    · simpa using negSign (ha 0 i)
    · simpa using ha 1 i
    · simpa using ha 2 i
  · intro x
    change -(v x) = _
    rw [h]
    simp [Fin.prod_univ_succ]

/-- Chart image of the full real local polytope, including all nondeterministic points. -/
theorem chartPolytope_eq_rectangle :
    chartPolytope = (Icc (-8) 8) ×ˢ (Icc (-12) 12) := by
  let L : V →ₗ[ℝ] ℝ × ℝ := (d0.prod d13).toLinearMap
  have lin (v : V) : L v = chart v := rfl
  have cP : Convex ℝ chartPolytope := (convex_convexHull ℝ (strategySet 3 4)).linear_image L
  have box : Convex ℝ ((Icc (-8 : ℝ) 8) ×ˢ (Icc (-12 : ℝ) 12)) :=
    (convex_Icc (-8 : ℝ) 8).prod (convex_Icc (-12 : ℝ) 12)
  apply Set.Subset.antisymm
  · rintro _ ⟨v,hv,rfl⟩
    have contained : strategySet 3 4 ⊆ L ⁻¹' (Icc (-8) 8 ×ˢ Icc (-12) 12) := by
      intro p hp
      have pos := d0_le (subset_convexHull ℝ _ hp)
      have neg := d0_le (subset_convexHull ℝ _ (neg_strategy hp))
      rw [map_neg] at neg
      change (-8 ≤ d0 p ∧ d0 p ≤ 8) ∧ (-12 ≤ d13 p ∧ d13 p ≤ 12)
      exact ⟨⟨by linarith, pos⟩, d13_bounds_atom hp⟩
    exact convexHull_min contained (box.linear_preimage L) hv
  · have corners : ({-8,8} : Set ℝ) ×ˢ ({-12,12} : Set ℝ) ⊆ chartPolytope := by
      rintro ⟨x,y⟩ ⟨hx,hy⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · refine ⟨atom ![true,true,true,true] ![true,true,true,true] ![true,true,true,false],
            atom_mem _ _ _, ?_⟩
        norm_num [chart,d0,d13,block000,block011,block101,block110,mermin,atom,signValue]
      · refine ⟨atom ![true,true,false,true] ![true,true,false,true] ![true,false,false,true],
            atom_mem _ _ _, ?_⟩
        norm_num [chart,d0,d13,block000,block011,block101,block110,mermin,atom,signValue]
      · refine ⟨atom ![true,true,false,true] ![true,true,false,true] ![false,true,true,false],
            atom_mem _ _ _, ?_⟩
        norm_num [chart,d0,d13,block000,block011,block101,block110,mermin,atom,signValue]
      · exact top_mem.1
    have h := convexHull_min corners cP
    rw [convexHull_prod, convexHull_pair, convexHull_pair,
      segment_eq_Icc (by norm_num : (-8 : ℝ) ≤ 8),
      segment_eq_Icc (by norm_num : (-12 : ℝ) ≤ 12)] at h
    exact h

end Lemmata.SymmetricBellFacetLifting.Facets
