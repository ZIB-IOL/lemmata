module
public import Lemmata.BellFollowup.Positive.Strategy
public import Lemmata.BellFollowup.Positive.Main

@[expose] public section
noncomputable section
open Set BigOperators
namespace Lemmata.BellFollowup.Positive.Archive.M3
open SymmetricBellCrossPolytope
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def B (i : Fin 2) (x : Index 3) : ℤ :=
  let n := (x 0).val + (x 1).val + (x 2).val
  (-1) ^ (n / 3) * (if n % 3 = i.val then 1 else if i.val > 0 ∧ 3 - n % 3 = i.val then -1 else 0)

private def A (i : Fin 2) (x : Index 3) : ℤ :=
  ∑ r : Fin 2, (![![(18),(9)],![(6),(-5)]] : Fin 2 → Fin 2 → ℤ) i r * B r x

private def C : Fin 2 → Fin 2 → ℤ := ![![(5),(9)],![(6),(-18)]]
private def R (r : Fin 2) : Index 3 := ![0,0,Fin.ofNat 3 r.val]
private def W (x : Index 3) : List (Fin 4) :=
  ([
    [],[],[3],[1],[3,2,1,2],[0,1,2],[1,3],[1,1,2],[2,1,2],[0,1],
    [1,3,2,1],[1,2],[3,2,1],[2,1,0,2],[1,2],[0,2],[0,2],[3,2],[0,1,3],[1,0,2],
    [1,2,1],[2],[2],[2,3],[2,1],[1,3,2],[2,0,1,2]] : List (List (Fin 4)))[(x 0).val*9+(x 1).val*3+(x 2).val]!

private theorem ok : generatorOK 3 := by
  have h : ∀ i : Fin 4, ∀ x : Index 3,
      ending ((![ [0],[1,1],List.replicate 2 2,[3]] : Fin 4 → List (Fin 4)) i) (idx i x) = x := by decide +kernel
  exact ⟨fun i => (show Function.LeftInverse _ _ from h i).injective, by decide +kernel⟩

private theorem basis_fixed (i : Fin 2) : ivec (A i) ∈ symSub 3 3 :=
  fixed_of_equivariance ok _ ((show ∀ (i : Fin 2) j x, weight j x * A i x = A i (idx j x) by decide +kernel) i)

private theorem basis_span : ∀ p ∈ symSub 3 3,
    p ∈ Submodule.span ℝ (range (fun j => ivec (A j))) := by
  apply span_of_reconstruction A B R C 144 (by decide) (by decide +kernel)
  apply expand_fixed ok R B W
  decide +kernel

private theorem compute (a b c : Fin 3 → ℤ) :
    List.ofFn (score A a b c) = integerImage inv3 (threeCoords 3 (List.ofFn a) (List.ofFn b) (List.ofFn c)) := by
  change [score A a b c 0, score A a b c 1] = _
  simp only [score, sum_indices]
  have hr : List.range 3 = [0,1,2] := by decide
  have hd : List.range 2 = [0,1] := by decide
  norm_num [hr, hd, Fin.sum_univ_succ, List.ofFn_succ, A, B, integerImage, inv3,
    threeCoords, ncMul, evenCoords, List.zipWith, List.getElem!_cons_zero, List.getElem!_cons_succ] <;> (repeat' constructor) <;> ring

/-- The full archive affine-equivalence statement at three parties and 3 settings. -/
theorem positive : ∃ f : Tensor 3 3 →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2),
    InjOn f (Gamma 3 3 '' localPolytope 3 3) ∧
    f '' (Gamma 3 3 '' localPolytope 3 3) = crossPolytope 2 :=
  archive_equivalence (D := 144) (by decide) _ _ basis_fixed basis_span compute positive_3

end Lemmata.BellFollowup.Positive.Archive.M3
