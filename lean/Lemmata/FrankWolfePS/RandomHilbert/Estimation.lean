module
public import Lemmata.FrankWolfePS.Unique.Lower
/-! The finite posterior bound for estimating the hidden barycenter, with arbitrary estimates. -/
@[expose] public section
namespace Lemmata.FrankWolfePS.RandomHilbert
open Finset
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bary_sq {I : Finset ι} (hne : I.Nonempty) :
    sq (simplexBarycenter I) = 1 / (I.card : ℝ) := by
  have hc : (I.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hne).ne'
  simp only [sq, simplexBarycenter, ite_pow, zero_pow (by decide : 2 ≠ 0)]
  simp [hc, pow_two]

/-- Low posterior mass entails squared error at least 1/(128k) for the actual,
untruncated estimator. The finite posterior theorem uses the clipped absolute guess. -/
theorem mass_estimation {k : ℕ} (hk : 0<k) {I : Finset ι} (hc : I.card=8*k) (z : Pt ι)
    (hm : ∑ i ∈ I, guess k z i ≤ 3/4) :
    1/(128*(k:ℝ)) ≤ sq (fun i => z.1 i-simplexBarycenter I i) := by
  let v := simplexBarycenter I
  have ne : I.Nonempty := card_pos.mp (by omega)
  have kp : 0<(k:ℝ) := by exact_mod_cast hk
  have kc : (I.card:ℝ)=8*k := by exact_mod_cast hc
  have bv : (8*(k:ℝ))*sq v=1 := by rw [show sq v = _ from bary_sq ne,kc]; field_simp
  by_contra! close
  have ce := (lt_div_iff₀ (by positivity : 0<(128:ℝ)*k)).mp close
  have young : 2*sq z.1 ≤ 3*sq v + 6*sq (fun i => z.1 i-v i) := by
    simp only [sq, mul_sum, ← sum_add_distrib]
    apply sum_le_sum; intro i _
    nlinarith [_root_.sq_nonneg (2*z.1 i-3*v i)]
  have yz := mul_le_mul_of_nonneg_left young kp.le
  have cut : 4*(k:ℝ)*sq z.1 ≤ 1 := by nlinarith only [ce,bv,yz]
  have low : ∑ i ∈ I,z.1 i ≤ 3/4 :=
    (sum_le_sum (fun i _ => le_abs_self (z.1 i))).trans (by simpa [guess,cut] using hm)
  have deficit : 1/4 ≤ ∑ i ∈ I,(v i-z.1 i) := by
    rw [sum_sub_distrib,(barycenter_base ne).2.2]; linarith
  have cs : (∑ i ∈ I,(v i-z.1 i))^2 ≤ (I.card:ℝ)*∑ i ∈ I,(v i-z.1 i)^2 := sq_sum_le_card_mul_sum_sq
  have sub : ∑ i ∈ I,(v i-z.1 i)^2 ≤ sq (fun i => z.1 i-v i) := by
    simp only [sub_sq_comm (v _) (z.1 _)]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => _root_.sq_nonneg _
  rw [kc] at cs
  nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/4) deficit 2,cs,
    mul_le_mul_of_nonneg_left sub (by positivity : 0≤(8:ℝ)*k),ce]

theorem finite_estimation (T : ℕ) (a : ι) (N : Fintype.card ι=256*(T+1))
    (s : Orders ι (Pt ι) T) :
    ((instanceSets T a).card:ℝ)/4 ≤ ∑ J ∈ instanceSets T a,
      flag (1/(128*((T+1:ℕ):ℝ)) ≤ sq (fun i =>
        (s.run (insert a J)).1 i-simplexBarycenter (insert a J) i)) :=
  fixed_tape_mass T a N _ (fun _ z h m => mass_estimation (Nat.succ_pos _) h z m) s

end Lemmata.FrankWolfePS.RandomHilbert
