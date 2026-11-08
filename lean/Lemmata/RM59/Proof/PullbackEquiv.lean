module

public import Lemmata.RM59.Proof.SupportForms

@[expose] public section

namespace Lemmata.RM59.SupportForms

@[simp] theorem pullback_id :
    pullback (LinearMap.id : Point 9 →ₗ[Field] Point 9) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  funext i
  change evaluation (Pi.single i 1) a = a i
  rw [evaluation_comm, evaluation_single]

theorem pullback_comp (g h : Point 9 →ₗ[Field] Point 9) :
    pullback (g.comp h) = (pullback h).comp (pullback g) := by
  apply LinearMap.ext
  intro a
  funext i
  change evaluation (g (h (Pi.single i 1))) a =
    evaluation (h (Pi.single i 1)) (pullback g a)
  exact evaluation_map g (h (Pi.single i 1)) a

@[simp] theorem pullback_pullback (g : Point 9 →ₗ[Field] Point 9) :
    pullback (pullback g) = g := by
  apply LinearMap.ext
  intro x
  funext i
  change evaluation (pullback g (Pi.single i 1)) x = (g x) i
  rw [evaluation_comm, ← evaluation_map, evaluation_single]

theorem pullback_injective : Function.Injective pullback := by
  intro g h heq
  have heq' := congrArg pullback heq
  simpa only [pullback_pullback] using heq'

theorem pullback_surjective : Function.Surjective pullback :=
  fun g => ⟨pullback g, pullback_pullback g⟩

def pullbackEquiv (e : Point 9 ≃ₗ[Field] Point 9) : Point 9 ≃ₗ[Field] Point 9 :=
  LinearEquiv.ofLinearMap (pullback e.toLinearMap) (pullback e.symm.toLinearMap)
    (by rw [← pullback_comp, LinearEquiv.symm_comp, pullback_id])
    (by rw [← pullback_comp, LinearEquiv.comp_symm, pullback_id])

@[simp] theorem pullbackEquiv_toLinearMap (e : Point 9 ≃ₗ[Field] Point 9) :
    (pullbackEquiv e).toLinearMap = pullback e.toLinearMap := rfl

@[simp] theorem pullbackEquiv_apply (e : Point 9 ≃ₗ[Field] Point 9) (x : Point 9) :
    pullbackEquiv e x = pullback e.toLinearMap x := rfl

theorem pullbackEquiv_symm (e : Point 9 ≃ₗ[Field] Point 9) :
    (pullbackEquiv e).symm = pullbackEquiv e.symm := by
  apply LinearEquiv.ext
  intro x
  rfl

@[simp] theorem pullbackEquiv_pullbackEquiv (e : Point 9 ≃ₗ[Field] Point 9) :
    pullbackEquiv (pullbackEquiv e) = e := by
  apply LinearEquiv.ext
  intro x
  change pullback (pullback e.toLinearMap) x = e x
  exact congrArg (fun f : Point 9 →ₗ[Field] Point 9 => f x)
    (pullback_pullback e.toLinearMap)

theorem pullbackEquiv_trans (e f : Point 9 ≃ₗ[Field] Point 9) :
    pullbackEquiv (e.trans f) = (pullbackEquiv f).trans (pullbackEquiv e) := by
  apply LinearEquiv.ext
  intro x
  change pullback (f.toLinearMap.comp e.toLinearMap) x =
    pullback e.toLinearMap (pullback f.toLinearMap x)
  exact congrArg (fun g : Point 9 →ₗ[Field] Point 9 => g x)
    (pullback_comp f.toLinearMap e.toLinearMap)

theorem pullbackEquiv_surjective : Function.Surjective pullbackEquiv :=
  fun e => ⟨pullbackEquiv e, pullbackEquiv_pullbackEquiv e⟩

theorem supportForm_image_pullbackEquiv (P : Finset (Point 9))
    (e : Point 9 ≃ₗ[Field] Point 9) :
    supportForm (P.image (pullbackEquiv e)) =
      (supportForm P).compLinearMap fun _ => e.toLinearMap := by
  change supportForm (P.image (pullback e.toLinearMap)) =
    (supportForm P).compLinearMap fun _ => e.toLinearMap
  simpa only [pullback_pullback] using
    supportForm_image P (pullback e.toLinearMap) (pullbackEquiv e).injective

theorem alternatingSupportForm_image_pullbackEquiv (P : Finset (Point 9))
    (hP : LowerZero P) (e : Point 9 ≃ₗ[Field] Point 9) :
    alternatingSupportForm (P.image (pullbackEquiv e))
      (lowerZero_image P hP (pullbackEquiv e).toLinearMap (pullbackEquiv e).injective) =
        (alternatingSupportForm P hP).compLinearMap e.toLinearMap := by
  apply AlternatingMap.coe_multilinearMap_injective
  exact supportForm_image_pullbackEquiv P e

theorem matchSupportMoments_image {P Q : Finset (Point 9)}
    (hPQ : MatchSupportMoments 3 P Q) (g : Point 9 →ₗ[Field] Point 9)
    (hg : Function.Injective g) :
    MatchSupportMoments 3 (P.image g) (Q.image g) := by
  apply matchSupportMoments_of_supportForm_eq
  · rw [supportForm_image P g hg, supportForm_image Q g hg,
      supportForm_eq_of_matchSupportMoments hPQ]
  · simp only [supportMoment_empty_index]
    rw [Finset.card_image_of_injective P hg, Finset.card_image_of_injective Q hg]
    simpa only [supportMoment_empty_index] using hPQ ∅ (by simp)

theorem matchSupportMoments_translate (P : Finset (Point 9)) (hP : LowerZero P)
    (t : Point 9) : MatchSupportMoments 3 (translateSupport P t) P := by
  apply matchSupportMoments_of_supportForm_eq (supportForm_translate P hP t)
  have hinj : Function.Injective (fun x : Point 9 => x + t) :=
    fun _ _ h => add_right_cancel h
  rw [supportMoment_empty_index, supportMoment_empty_index, translateSupport,
    Finset.card_image_of_injective P hinj]

end Lemmata.RM59.SupportForms
