module

public import Lemmata.Centroid.Proof.General.HigherRadicalNumeric
public import Lemmata.Centroid.Proof.General.ProjectedTensor
public import Lemmata.Centroid.Proof.Tensor.SharpSupportBound

@[expose] public section

open scoped BigOperators Matrix
open Classical

noncomputable section

namespace Lemmata.Centroid.General

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A] [FiniteDimensional F A]

theorem annihilator_dimension_lt_of_square_ne_bot (I : Ideal A) (hI : I * I ≠ ⊥) :
    Module.finrank F (annihilatorInIdeal I) < Module.finrank F I := by
  have hne : annihilatorInIdeal I ≠ I := by
    intro heq
    apply hI
    apply bot_unique
    apply Ideal.mul_le.mpr
    intro a ha b hb
    have ha' : a ∈ annihilatorInIdeal I := by rw [heq]; exact ha
    exact congrArg Subtype.val ((Module.mem_annihilator.mp ha'.2) ⟨b, hb⟩)
  have hstrict : (annihilatorInIdeal I).restrictScalars F < I.restrictScalars F := by
    apply lt_of_le_of_ne (fun _ hx => hx.1)
    intro heq
    apply hne
    ext c
    change c ∈ (annihilatorInIdeal I).restrictScalars F ↔ c ∈ I.restrictScalars F
    rw [heq]
  exact Submodule.finrank_lt_finrank_of_lt hstrict

end Lemmata.Centroid.General

namespace Lemmata.Centroid.Tensor.BalancedAlgebra

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]
variable {V : Fin 3 → Type*} [∀ i, Fintype (V i)]
variable (T : Tensor F (Fin 3) V) (hT : Concise T)
variable (f : A →ₐ[F] centroidAlgebra T hT)

theorem kernel_le_annihilatorKernel (I : Ideal A) (i : Fin 3) :
    commonKernel (idealSpace T hT f I) i ≤
      commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) i := by
  intro u hu
  rw [mem_commonKernel] at hu ⊢
  rintro _ ⟨c, hc, rfl⟩
  exact hu (f c).val ⟨c, hc.1, rfl⟩

theorem idealSpace_mul_annihilator (I : Ideal A)
    {C D : ∀ i, Matrix (V i) (V i) F}
    (hC : C ∈ idealSpace T hT f I)
    (hD : D ∈ idealSpace T hT f (General.annihilatorInIdeal I)) : C * D = 0 := by
  obtain ⟨c, hc, rfl⟩ := hC
  obtain ⟨d, hd, rfl⟩ := hD
  have hdc : d * c = 0 := congrArg Subtype.val ((Module.mem_annihilator.mp hd.2) ⟨c, hc⟩)
  have hcd : c * d = 0 := by simpa only [mul_comm] using hdc
  change (f c * f d).val = 0
  rw [← map_mul, hcd, map_zero]
  rfl

theorem annihilator_image_oneSupportAt (I : Ideal A) (i : Fin 3) :
    oneSupportAt (imageAt T (idealSpace T hT f (General.annihilatorInIdeal I)) 0) i ≤
      commonKernel (idealSpace T hT f I) i := by
  apply oneSupportAt_le_commonKernel
  intro C hC U hU
  rw [imageAt_eq (idealSpace_le T hT f (General.annihilatorInIdeal I)) 0 i] at hU
  obtain ⟨D, hD, rfl⟩ := hU
  change legAction (legAction T i (D i)) i (C i) = 0
  rw [← legAction_mul]
  have hCD := congrFun (idealSpace_mul_annihilator T hT f I hC hD) i
  change C i * D i = 0 at hCD
  rw [hCD, map_zero]

variable [FiniteDimensional F A]

omit [FiniteDimensional F A] in
theorem annihilator_support_budget_bound (hf : Function.Injective f) (I : Ideal A)
    (N d : ℕ) (hformat : ∀ i, Fintype.card (V i) ≤ N)
    (hd : ∀ i, d ≤
      Module.finrank F (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) i) -
        Module.finrank F (commonKernel (idealSpace T hT f I) i)) :
    Module.finrank F (General.annihilatorInIdeal I) ≤ supportBound (N - d) := by
  let J := idealSpace T hT f (General.annihilatorInIdeal I)
  let S := imageAt T J 0
  have hbudget : ∀ i, Module.finrank F (oneSupportAt S i) +
      Module.finrank F (oppositeSupportAt S i) ≤ N - d := by
    intro i
    have hρ := Submodule.finrank_mono (annihilator_image_oneSupportAt T hT f I i)
    have hpair : Module.finrank F (oppositeSupportAt S i) =
        Fintype.card (V i) - Module.finrank F (commonKernel J i) := by
      change Module.finrank F (oppositeSupportAt (imageAt T J 0) i) = _
      rw [imageAt_eq (show J ≤ centroid T from idealSpace_le T hT f _) 0 i]
      exact finrank_oppositeSupportAt_imageAt hT J i
    have hkH := Submodule.finrank_mono (kernel_le_annihilatorKernel T hT f I i)
    have hH := finrank_rowSpace_add_commonKernel J i
    have hdi := hd i
    have hmi := hformat i
    change Module.finrank F (oneSupportAt S i) ≤
      Module.finrank F (commonKernel (idealSpace T hT f I) i) at hρ
    change d ≤ Module.finrank F (commonKernel J i) - _ at hdi
    change Module.finrank F (commonKernel (idealSpace T hT f I) i) ≤
      Module.finrank F (commonKernel J i) at hkH
    omega
  have h := support_budget_bound S (N - d) hbudget
  rw [finrank_imageAt hT (idealSpace_le T hT f _), idealSpace_finrank T hT f hf] at h
  exact h

theorem higher_radical_bound (hf : Function.Injective f) (I : Ideal A)
    (hI : IsNilpotent I) (hI₂ : I * I ≠ ⊥) (N : ℕ)
    (hformat : ∀ i, Fintype.card (V i) ≤ N) : Module.finrank F I ≤ generalBound N - 1 := by
  let K (i : Fin 3) := Module.finrank F (commonKernel (idealSpace T hT f I) i)
  let H (i : Fin 3) := Module.finrank F
    (commonKernel (idealSpace T hT f (General.annihilatorInIdeal I)) i)
  have hKH : ∀ i, K i ≤ H i := fun i =>
    Submodule.finrank_mono (kernel_le_annihilatorKernel T hT f I i)
  have hHm : ∀ i, H i ≤ Fintype.card (V i) := by
    intro i
    have hh := finrank_rowSpace_add_commonKernel
      (idealSpace T hT f (General.annihilatorInIdeal I)) i
    change _ + H i = _ at hh
    omega
  have hdim : ∀ i, K i + (H i - K i) + (Fintype.card (V i) - H i) = Fintype.card (V i) := by
    intro i
    have := hKH i
    have := hHm i
    omega
  have hq : ∀ i, (H i - K i) + (Fintype.card (V i) - H i) = Fintype.card (V i) - K i := by
    intro i
    have := hdim i
    omega
  let p : General.HigherRadicalProfile N :=
    { r := Module.finrank F I
      x := Module.finrank F I - Module.finrank F (General.annihilatorInIdeal I)
      y := Module.finrank F (General.annihilatorInIdeal I)
      m := fun i => Fintype.card (V i)
      k := K
      a := fun i => H i - K i
      b := fun i => Fintype.card (V i) - H i
      split := Nat.sub_add_cancel (General.annihilator_dimension_lt_of_square_ne_bot I hI₂).le
      xpos := Nat.sub_pos_iff_lt.mpr (General.annihilator_dimension_lt_of_square_ne_bot I hI₂)
      format := hformat
      dimensions := hdim
      kernel := fun i => by
        rw [hq]
        exact nilpotent_ideal_kernel_bound T hT f hf I hI i
      separation := fun i => by
        have h := nilpotent_ideal_annihilator_bound T hT f hf I hI i
        have heq : K i + (H i - K i) = H i := Nat.add_sub_of_le (hKH i)
        rw [heq, Nat.mul_comm]
        exact h
      difference := fun i => annihilator_difference_bound T hT f hf I i
      product := by
        simpa only [hq] using ideal_product_bound T hT f hf I
      socleProduct := ideal_product_bound T hT f hf (General.annihilatorInIdeal I)
      socleBudget := fun d hd => annihilator_support_budget_bound T hT f hf I N d hformat hd
      projected := fun Q i j k hij hik hjk hQi hx => by
        apply projected_support_Q_bound T hT f hf I hI i j k hij hik hjk Q
        · rwa [hq i] at hQi
        · exact hx }
  exact General.higher_radical_profile_bound p

end Lemmata.Centroid.Tensor.BalancedAlgebra
