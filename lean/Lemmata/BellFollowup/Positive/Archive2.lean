module
public import Lemmata.BellFollowup.Positive.Strategy
public import Lemmata.BellFollowup.Positive.Main

@[expose] public section
noncomputable section
open Set BigOperators
namespace Lemmata.BellFollowup.Positive.Archive.M2
open SymmetricBellCrossPolytope
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def B (i : Fin 1) (x : Index 2) : ℤ :=
  let n := (x 0).val + (x 1).val + (x 2).val
  (-1) ^ (n / 2) * (if n % 2 = i.val then 1 else if i.val > 0 ∧ 2 - n % 2 = i.val then -1 else 0)

private def A (i : Fin 1) (x : Index 2) : ℤ :=
  ∑ r : Fin 1, (![![(2)]] : Fin 1 → Fin 1 → ℤ) i r * B r x

private def C : Fin 1 → Fin 1 → ℤ := ![![(1)]]
private def R (r : Fin 1) : Index 2 := ![0,0,Fin.ofNat 2 r.val]
private def W (x : Index 2) : List (Fin 4) :=
  ([
    [],[3],[3],[0,1,2],[3],[1,2],[2],[3]] : List (List (Fin 4)))[(x 0).val*4+(x 1).val*2+(x 2).val]!

private theorem ok : generatorOK 2 := by
  have h : ∀ i : Fin 4, ∀ x : Index 2,
      ending ((![ [0],[1,1],List.replicate 1 2,[3]] : Fin 4 → List (Fin 4)) i) (idx i x) = x := by decide +kernel
  exact ⟨fun i => (show Function.LeftInverse _ _ from h i).injective, by decide +kernel⟩

private theorem basis_fixed (i : Fin 1) : ivec (A i) ∈ symSub 3 2 :=
  fixed_of_equivariance ok _ ((show ∀ (i : Fin 1) j x, weight j x * A i x = A i (idx j x) by decide +kernel) i)

private theorem basis_span : ∀ p ∈ symSub 3 2,
    p ∈ Submodule.span ℝ (range (fun j => ivec (A j))) := by
  apply span_of_reconstruction A B R C 2 (by decide) (by decide +kernel)
  apply expand_fixed ok R B W
  decide +kernel

private theorem compute (a b c : Fin 2 → ℤ) :
    List.ofFn (score A a b c) = integerImage inv2 (threeCoords 2 (List.ofFn a) (List.ofFn b) (List.ofFn c)) := by
  change [score A a b c 0] = _
  simp only [score, sum_indices]
  have hr : List.range 2 = [0,1] := by decide
  have hd : List.range 1 = [0] := by decide
  norm_num [hr, hd, Fin.sum_univ_succ, List.ofFn_succ, A, B, integerImage, inv2,
    threeCoords, ncMul, evenCoords, List.zipWith, List.getElem!_cons_zero, List.getElem!_cons_succ] <;> (repeat' constructor) <;> ring

/-- The full archive affine-equivalence statement at three parties and 2 settings. -/
theorem positive : ∃ f : Tensor 3 2 →ᵃ[ℝ] EuclideanSpace ℝ (Fin 1),
    InjOn f (Gamma 3 2 '' localPolytope 3 2) ∧
    f '' (Gamma 3 2 '' localPolytope 3 2) = crossPolytope 1 :=
  archive_equivalence (D := 4) (by decide) _ _ basis_fixed basis_span compute positive_2

end Lemmata.BellFollowup.Positive.Archive.M2
