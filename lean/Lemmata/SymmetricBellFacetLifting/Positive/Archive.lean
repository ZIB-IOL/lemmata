module

public import Lemmata.SymmetricBellCrossPolytope.Main
public import Lemmata.SymmetricBellFacetLifting.Positive.Hull

@[expose] public section
noncomputable section
open Set BigOperators
namespace Lemmata.SymmetricBellFacetLifting.Positive.Archive
open SymmetricBellCrossPolytope

abbrev Index (m : Nat) := Fin 3 → Fin m
def ivec {m : Nat} (f : Index m → ℤ) : Tensor 3 m :=
  WithLp.toLp 2 (fun x => (f x : ℝ))

def idx {m : Nat} (i : Fin 4) (x : Index m) : Index m := (gen i x).2
def wrap (m : Nat) (q : ℤ) : ℤ := (-1) ^ (q / (m : ℤ)).natAbs
def weight {m : Nat} (i : Fin 4) (x : Index m) : ℤ :=
  ![(1:ℤ),1,∏ n : Fin 3, wrap m ((x n : ℤ) + if n.val = 0 then 1 else if n.val = 1 then -1 else 0),
    ∏ n : Fin 3, -(wrap m ((m:ℤ)-(x n : ℤ)))] i

theorem weight_cast {m : Nat} (i : Fin 4) (x : Index m) :
    (weight i x : ℝ) = (gen i x).1 := by
  have hw (q : ℤ) : (wrap m q : ℝ) = (-1 : ℝ) ^ (q / (m : ℤ)) := by
    simp only [wrap, neg_one_pow_eq_ite, neg_one_zpow_eq_ite, Int.natAbs_even]
    split <;> norm_num
  fin_cases i
  · change ((1:ℤ):ℝ) = 1; norm_num
  · change ((1:ℤ):ℝ) = 1; norm_num
  · simp [weight, gen, gen3, shiftParty, reduceIdx, normIdx, hw]
  · simp [weight, gen, gen4, reduceIdx, normIdx, hw]

def ending {m : Nat} : List (Fin 4) → Index m → Index m
 | [], x => x
 | i::w, x => ending w (idx i x)
def factor {m : Nat} : List (Fin 4) → Index m → ℤ
 | [], _ => 1
 | i::w, x => weight i x * factor w (idx i x)

def generatorOK (m : Nat) :=
  (∀ i : Fin 4, Function.Injective (@idx m i)) ∧
  (∀ (i : Fin 4) (x : Index m), weight i x * weight i x = 1)

theorem act_at {m : Nat} (h : generatorOK m) (i : Fin 4) (p : Tensor 3 m) (x : Index m) :
    act (gen i) p (idx i x) = (weight i x : ℝ) * p x := by
  classical
  change (∑ z : Index m, if idx i z = idx i x then (gen i z).1 * p z else 0) = _
  rw [Finset.sum_eq_single x, ite_eq_left rfl, weight_cast]
  · intro y _ ne; exact ite_eq_right (fun e => ne (h.1 i e))
  · simp

theorem along {m : Nat} (h : generatorOK m) (p : Tensor 3 m) (hp : p ∈ symSub 3 m)
    (w : List (Fin 4)) (x : Index m) :
    p x = (factor w x : ℝ) * p (ending w x) := by
  induction w generalizing x with
  | nil => simp [factor,ending]
  | cons i w ih =>
    have hh := congrArg (fun q : Tensor 3 m => q (idx i x)) (hp i)
    change act _ p (idx i x) = p (idx i x) at hh
    rw [act_at h] at hh
    have hs : (weight i x : ℝ) * (weight i x : ℝ) = 1 := by exact_mod_cast h.2 i x
    simp only [factor, ending, Int.cast_mul]
    rw [mul_assoc, ← ih (idx i x), ← hh, ← mul_assoc, hs, one_mul]

theorem fixed_of_equivariance {m : Nat} (h : generatorOK m) (f : Index m → ℤ)
    (he : ∀ i x, weight i x * f x = f (idx i x)) : ivec f ∈ symSub 3 m := by
  intro i
  apply PiLp.ext
  intro y
  obtain ⟨x,rfl⟩ := Finite.surjective_of_injective (h.1 i) y
  rw [act_at h]
  change (weight i x : ℝ) * (f x : ℝ) = (f (idx i x) : ℝ)
  exact_mod_cast he i x

/-- A word for each entry gives a proof of the signed orbit expansion.
If a stabilizing word reverses the sign, that orbit vanishes. -/
theorem expand_fixed {m d : Nat} (h : generatorOK m)
    (R : Fin d → Index m) (B : Fin d → Index m → ℤ)
    (W : Index m → List (Fin 4))
    (hc : ∀ x, (∃ r, ending (W x) x = R r ∧
        ∀ j, B j x = if j = r then factor (W x) x else 0) ∨
      (ending (W x) x = x ∧ factor (W x) x = -1 ∧ ∀ j, B j x = 0))
    (p : Tensor 3 m) (hp : p ∈ symSub 3 m) :
    p = ∑ r, p (R r) • ivec (B r) := by
  apply PiLp.ext
  intro x
  have hw := along h p hp (W x) x
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, ivec, PiLp.toLp_apply, smul_eq_mul]
  rcases hc x with ⟨r, hR, hb⟩ | ⟨he,hs,hb⟩
  · simp_rw [hb]
    simpa [hR, mul_comm] using hw
  · rw [he,hs] at hw
    simp [hb]
    push_cast at hw
    linarith

/-- Turn a finite integer change-of-basis certificate into a span assertion. -/
theorem span_of_reconstruction {m d : Nat} (A B : Fin d → Index m → ℤ)
    (R : Fin d → Index m) (C : Fin d → Fin d → ℤ) (D : ℕ) (hD : 0 < D)
    (matrix : ∀ r x, (D:ℤ) * B r x = ∑ j, C r j * A j x)
    (expansion : ∀ p ∈ symSub 3 m, p = ∑ r, p (R r) • ivec (B r)) :
    ∀ p ∈ symSub 3 m, p ∈ Submodule.span ℝ (range (fun j => ivec (A j))) := by
  let K := Submodule.span ℝ (range (fun j => ivec (A j)))
  have mem (r) : ivec (B r) ∈ K := by
    have eqn : ivec (B r) = ((D : ℝ)⁻¹) • ∑ j, (C r j : ℝ) • ivec (A j) := by
      apply PiLp.ext
      intro x
      simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, ivec, PiLp.toLp_apply, smul_eq_mul]
      have hm : (D : ℝ) * (B r x : ℝ) = ∑ j, (C r j : ℝ) * (A j x : ℝ) := by
        exact_mod_cast matrix r x
      rw [← hm, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hD.ne'), one_mul]
    rw [eqn]
    exact K.smul_mem _ (K.sum_mem (fun j _ => K.smul_mem _
      (Submodule.subset_span (Set.mem_range_self j))))
  intro p hp
  rw [expansion p hp]
  exact K.sum_mem (fun i _ => K.smul_mem _ (mem i))

def linearChart {m d : Nat} (A : Fin d → Index m → ℤ) (D : ℕ) :
    Tensor 3 m →ₗ[ℝ] (Fin d → ℝ) :=
  LinearMap.pi (fun i => (D : ℝ)⁻¹ • (innerSL ℝ (ivec (A i))).toLinearMap)

theorem chartValue {m d} (A : Fin d → Index m → ℤ) (D : ℕ) (p : Tensor 3 m) (i : Fin d) :
    linearChart A D p i = inner ℝ (ivec (A i)) p / D := by
  change (D : ℝ)⁻¹ * inner ℝ (ivec (A i)) p = _
  rw [div_eq_mul_inv, mul_comm]

theorem chart_project {m d} (A : Fin d → Index m → ℤ) (D : ℕ)
    (hf : ∀ j, ivec (A j) ∈ symSub 3 m) (p : Tensor 3 m) :
    linearChart A D (Gamma 3 m p) = linearChart A D p := by
  ext i
  simp only [chartValue]
  have hh := Submodule.starProjection_inner_eq_zero (K := symSub 3 m) p _ (hf i)
  change inner ℝ (p - Gamma 3 m p) (ivec (A i)) = 0 at hh
  rw [inner_sub_left] at hh
  congr 1
  calc
    _ = inner ℝ (Gamma 3 m p) (ivec (A i)) := real_inner_comm ..
    _ = inner ℝ p (ivec (A i)) := (sub_eq_zero.mp hh).symm
    _ = _ := real_inner_comm ..

theorem chart_inj {m d} (A : Fin d → Index m → ℤ) (D : ℕ) (hD : 0 < D)
    (hs : ∀ p ∈ symSub 3 m, p ∈ Submodule.span ℝ (range (fun j => ivec (A j)))) :
    Set.InjOn (linearChart A D) (Gamma 3 m '' localPolytope 3 m) := by
  rintro x ⟨x',_,rfl⟩ y ⟨y',_,rfl⟩ he
  let z := Gamma 3 m x' - Gamma 3 m y'
  have hz : z ∈ symSub 3 m := (symSub 3 m).sub_mem
    ((symSub 3 m).starProjection_apply_mem _) ((symSub 3 m).starProjection_apply_mem _)
  have ho (i : Fin d) : inner ℝ (ivec (A i)) z = 0 := by
    have hx := congrFun he i
    simp only [chartValue] at hx
    have hne : (D:ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    simpa [z, inner_sub_right] using sub_eq_zero.mpr ((div_left_inj' hne).mp hx)
  have hh : ∀ b ∈ Submodule.span ℝ (range (fun j => ivec (A j))), inner ℝ b z = 0 := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b h => obtain ⟨i,rfl⟩ := h; exact ho i
    | zero => simp
    | add a b _ _ ha hb => simp [inner_add_left, ha, hb]
    | smul k a _ ha => simp [real_inner_smul_left, ha]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (hh z (hs z hz)))

end Lemmata.SymmetricBellFacetLifting.Positive.Archive
