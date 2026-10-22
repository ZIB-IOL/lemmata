module

public import Lemmata.Centroid.Proof.Linear.MaximalRank

@[expose] public section

open scoped BigOperators Matrix
open Polynomial Classical
noncomputable section
namespace Lemmata.Centroid.Linear
variable {F : Type*} [Field F] {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem maximal_rank_kernel_lift [Infinite F] (A B : Matrix κ ι F)
    (hmax : ∀ t : F, (A + t • B).rank ≤ A.rank)
    (v : ι → F) (hv : A *ᵥ v = 0) :
    ∃ p : ι → F[X], (∀ i, (p i).eval 0 = v i) ∧
      pencil A B *ᵥ p = 0 := by
  classical
  obtain ⟨u, l, hbase⟩ := exists_identity_pivot A.mulVecLin
  change ∀ i, l (A *ᵥ u i) = Pi.single i 1 at hbase
  let J := Fin (Module.finrank F (LinearMap.range A.mulVecLin))
  let M : Matrix J J F[X] := fun j i =>
    C ((Pi.single i (1 : F) : J → F) j) + X * C (l (B *ᵥ u i) j)
  have hM (t : F) : M.map (evalRingHom t) =
      (fun j i => l ((A + t • B) *ᵥ u i) j) := by
    funext j i
    change (evalRingHom t) (M j i) = _
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, l.map_add, l.map_smul, hbase i]
    change (evalRingHom t) (M j i) = (Pi.single i (1 : F) : J → F) j +
      t * l (B *ᵥ u i) j
    simp [M]
    ring
  have hMzero : M.map (evalRingHom (0 : F)) = 1 := by
    funext j i
    change (evalRingHom (0 : F)) (M j i) = _
    by_cases h : j = i <;> simp [M, Pi.single_apply, Matrix.one_apply, h]
  have hdetzero : M.det.eval 0 = 1 := by
    change (evalRingHom (0 : F)) M.det = 1
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hMzero, Matrix.det_one]
  have hdet : M.det ≠ 0 := by
    intro h
    simp [h] at hdetzero
  let e : J → F[X] := fun j => X * C (l (B *ᵥ v) j)
  let c := M.adjugate *ᵥ e
  have hc : M *ᵥ c = M.det • e := by
    dsimp only [c]
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hce (t : F) : M.map (evalRingHom t) *ᵥ (fun i => (c i).eval t) =
      M.det.eval t • (fun i => (e i).eval t) := by
    funext j
    have h := congrArg (fun p : F[X] => p.eval t) (congrFun hc j)
    simpa [Matrix.mulVec, dotProduct, Polynomial.eval_finsetSum] using h
  let p : ι → F[X] := fun j =>
    M.det * C (v j) - ∑ i, c i * C (u i j)
  have hp (t : F) : (fun j => (p j).eval t) =
      M.det.eval t • v - ∑ i, (c i).eval t • u i := by
    funext j
    simp [p, Finset.sum_apply, Polynomial.eval_finsetSum]
  refine ⟨p, ?_, ?_⟩
  · intro j
    have hc0 (i : J) : (c i).eval 0 = 0 := by
      simp [c, Matrix.mulVec, dotProduct, e, Polynomial.eval_finsetSum]
    simp [p, hc0, hdetzero, Polynomial.eval_finsetSum]
  · funext j
    apply polynomial_eq_zero_of_eval_zero_where hdet
    intro t ht
    have hMt : (M.map (evalRingHom t)).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact ht
    let ft := (A + t • B).mulVecLin
    have hdim : Module.finrank F (LinearMap.range ft) ≤
        Fintype.card (Fin A.rank) := by
      change (A + t • B).rank ≤ Fintype.card (Fin A.rank)
      simpa only [Fintype.card_fin] using hmax t
    have hdet' : Matrix.det (fun j i => l (ft (u i)) j) ≠ 0 := by
      change Matrix.det (fun j i => l ((A + t • B) *ᵥ u i) j) ≠ 0
      rw [← hM]
      exact hMt
    have hinj := injective_on_range_of_pivot ft l u hdim hdet'
    have hlzero : l (ft (fun j => (p j).eval t)) = 0 := by
      rw [hp]
      simp only [map_sub, map_smul, map_sum]
      have hfv : l (ft v) = t • l (B *ᵥ v) := by
        change l ((A + t • B) *ᵥ v) = _
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, hv, zero_add, map_smul]
      rw [hfv]
      have hs : (∑ i, (c i).eval t • l (ft (u i))) =
          M.map (evalRingHom t) *ᵥ (fun i => (c i).eval t) := by
        rw [hM]
        funext k
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
          dotProduct]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
      rw [hs, hce]
      have he : (fun i => (e i).eval t) = t • l (B *ᵥ v) := by
        funext i
        simp [e]
        ring
      rw [he]
      exact sub_self _
    have hz : ft (fun j => (p j).eval t) = 0 := by
      have h : (⟨ft (fun j => (p j).eval t), LinearMap.mem_range_self ft _⟩ :
          LinearMap.range ft) = 0 := hinj (by simpa using hlzero)
      exact congrArg Subtype.val h
    change (evalRingHom t) ((pencil A B *ᵥ p) j) = 0
    rw [RingHom.map_mulVec, eval_pencil]
    exact congrFun hz j


end Lemmata.Centroid.Linear
