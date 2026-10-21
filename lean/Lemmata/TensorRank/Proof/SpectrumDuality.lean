module

public import Lemmata.TensorRank.Proof.SpectrumSaturation
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Monoid

@[expose] public section

set_option autoImplicit false

open Filter Set
open scoped Topology
open Classical

namespace Lemmata.TensorRank.Spectrum.StrassenPreorder

variable {S : Type*} [CommSemiring S] (p : StrassenPreorder S)

def pointOfExtension {q : StrassenPreorder S} (hpq : p ≤ q) (f : Point q) : Point p :=
  ⟨f.val, fun h => f.prop (hpq _ _ h)⟩

theorem exists_point : Nonempty (Point p) := by
  obtain ⟨q, hpq, hq⟩ := p.exists_maximal
  exact ⟨p.pointOfExtension hpq (q.pointOfTotal (q.maximal_total hq))⟩

theorem exists_point_ge_ratio (hp : p.OneLeNonzero) (a : S) (r s : ℕ) (hs : 0 < s)
    (hr : (r : ℝ) / s < p.asymptoticRank a) :
    ∃ f : Point p, (r : ℝ) / s ≤ f a := by
  let q := p.saturated
  have hnot : ¬ q.Rel ((s : S) * a) (r : S) := by
    intro h
    have hqpos : q.OneLeNonzero := p.oneLeNonzero_mono hp p.le_saturated
    have hh := q.asymptoticRank_mono h
    rw [q.asymptoticRank_nat_mul hqpos, q.asymptoticRank_nat,
      p.asymptoticRank_saturated hp] at hh
    exact (not_lt_of_ge hh) (by simpa only [mul_comm] using
      (div_lt_iff₀ (by exact_mod_cast hs : 0 < (s : ℝ))).mp hr)
  let t := q.comparisonExtension p.saturated_addCancellative
    p.saturated_mulCancellative ((s : S) * a) (r : S) hnot
  have hqt : q ≤ t := fun _ _ h => ⟨0, by simpa only [zero_mul, add_zero] using h⟩
  have hforce : t.Rel (r : S) ((s : S) * a) :=
    ⟨1, by convert q.refl ((r : S) + (s : S) * a) using 1 <;> ring⟩
  obtain ⟨u, htu, hu⟩ := t.exists_maximal
  let f := u.pointOfTotal (u.maximal_total hu)
  refine ⟨p.pointOfExtension (le_trans p.le_saturated (le_trans hqt htu)) f, ?_⟩
  have hf := f.prop (htu _ _ hforce)
  change (r : ℝ) / s ≤ f.val a
  apply (div_le_iff₀ (by exact_mod_cast hs : 0 < (s : ℝ))).mpr
  simpa only [map_natCast, map_mul, mul_comm] using hf

private theorem exists_nat_ratio_btwn {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    ∃ r s : ℕ, 0 < s ∧ x < (r : ℝ) / s ∧ (r : ℝ) / s < y := by
  obtain ⟨s, hs⟩ := exists_nat_gt (y - x)⁻¹
  have hspos : 0 < (s : ℝ) := (inv_pos.mpr (sub_pos.mpr hxy)).trans hs
  obtain ⟨z, hz, hzy⟩ := exists_div_btwn hxy hs
  have hzpos : 0 < (z : ℝ) := (div_pos_iff_of_pos_right hspos).mp (hx.trans_lt hz)
  have hznonneg : 0 ≤ z := by exact_mod_cast hzpos.le
  have he : (z.natAbs : ℝ) = (z : ℝ) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hznonneg]
  exact ⟨z.natAbs, s, by exact_mod_cast hspos, by rwa [he], by rwa [he]⟩

theorem exists_point_gt (hp : p.OneLeNonzero) (a : S) (x : ℝ) (hx : 0 ≤ x)
    (hxa : x < p.asymptoticRank a) : ∃ f : Point p, x < f a := by
  obtain ⟨r, s, hs, hxr, hra⟩ := exists_nat_ratio_btwn hx hxa
  obtain ⟨f, hf⟩ := p.exists_point_ge_ratio hp a r s hs hra
  exact ⟨f, hxr.trans_le hf⟩

def pointFunctions : Set (S → ℝ) :=
  {f | f 0 = 0 ∧ f 1 = 1 ∧ (∀ a b, f (a + b) = f a + f b) ∧
    (∀ a b, f (a * b) = f a * f b) ∧ ∀ a b, p.Rel a b → f a ≤ f b}

def pointOfFunction (f : S → ℝ) (hf : f ∈ p.pointFunctions) : Point p :=
  ⟨{ toFun := f
     map_zero' := hf.1
     map_one' := hf.2.1
     map_add' := hf.2.2.1
     map_mul' := hf.2.2.2.1 }, fun h => hf.2.2.2.2 _ _ h⟩

theorem mem_pointFunctions (f : Point p) : (fun a => f a) ∈ p.pointFunctions :=
  ⟨map_zero f.val, map_one f.val, map_add f.val, map_mul f.val, fun _ _ h => f.prop h⟩

theorem isClosed_pointFunctions : IsClosed p.pointFunctions := by
  unfold pointFunctions
  simp only [ofPred_and, ofPred_forall]
  apply (isClosed_eq (continuous_apply 0) continuous_const).inter
  apply (isClosed_eq (continuous_apply 1) continuous_const).inter
  apply (isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_eq (continuous_apply (a + b)) ((continuous_apply a).add (continuous_apply b))).inter
  apply (isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_eq (continuous_apply (a * b)) ((continuous_apply a).mul (continuous_apply b))).inter
  exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
    isClosed_le (continuous_apply a) (continuous_apply b)

theorem isCompact_pointFunctions : IsCompact p.pointFunctions := by
  have hb : IsCompact {f : S → ℝ | ∀ a, f a ∈ Icc 0 (p.rank a : ℝ)} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  apply hb.of_isClosed_subset p.isClosed_pointFunctions
  intro f hf a
  exact ⟨(p.pointOfFunction f hf).nonneg a, (p.pointOfFunction f hf).le_rank a⟩

theorem exists_point_eq_asymptoticRank (hp : p.OneLeNonzero) (a : S) :
    ∃ f : Point p, f a = p.asymptoticRank a := by
  obtain ⟨f₀⟩ := p.exists_point
  obtain ⟨f, hf, hmax⟩ := p.isCompact_pointFunctions.exists_isMaxOn
    ⟨fun a => f₀ a, p.mem_pointFunctions f₀⟩ (continuous_apply a).continuousOn
  let F := p.pointOfFunction f hf
  refine ⟨F, le_antisymm (F.le_asymptoticRank a) ?_⟩
  by_contra h
  obtain ⟨g, hg⟩ := p.exists_point_gt hp a (F a) (F.nonneg a) (lt_of_not_ge h)
  exact (not_lt_of_ge (hmax (p.mem_pointFunctions g))) hg

theorem asymptoticRank_le_iff (hp : p.OneLeNonzero) (a : S) (x : ℝ) :
    p.asymptoticRank a ≤ x ↔ ∀ f : Point p, f a ≤ x := by
  constructor
  · exact fun h f => (f.le_asymptoticRank a).trans h
  · intro h
    obtain ⟨f, hf⟩ := p.exists_point_eq_asymptoticRank hp a
    simpa only [hf] using h f

theorem asymptoticRank_eq_ciSup (hp : p.OneLeNonzero) (a : S) :
    p.asymptoticRank a = ⨆ f : Point p, f a := by
  obtain ⟨f, hf⟩ := p.exists_point_eq_asymptoticRank hp a
  let : Nonempty (Point p) := ⟨f⟩
  apply le_antisymm
  · rw [← hf]
    exact le_ciSup (show BddAbove (range fun g : Point p => g a) from
      ⟨p.rank a, by rintro _ ⟨g, rfl⟩; exact g.le_rank a⟩) f
  · exact ciSup_le (fun g => g.le_asymptoticRank a)

end Lemmata.TensorRank.Spectrum.StrassenPreorder
