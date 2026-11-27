module
public import Lemmata.FrankWolfePS.Unique.Replay
public import Mathlib.Topology.Maps.Proper.Basic
@[expose] public section
namespace Lemmata.FrankWolfePS.Unique
open Set MeasureTheory
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- A unique support selector is continuous off zero, including when the body
has no available description beyond its exact oracle. The value at zero can be public. -/
theorem measurable_reply {C : Set E} (hc : IsCompact C) {z : E} (hz : z ∈ C)
    (unique : ∀ q : E, q ≠ 0 → ∀ x y, MinAt C q x → MinAt C q y → x = y) :
    Measurable (reply C z) := by
  let S := ({0}ᶜ : Set E)
  let F : S → C := fun q => ⟨reply C z q.val, (reply_min hc hz q.val).1⟩
  let : CompactSpace C := isCompact_iff_compactSpace.mp hc
  have eq : F.graph = ⋂ y : C, {w : S × C | ⟪w.1.val, w.2.val⟫ ≤ ⟪w.1.val, y.val⟫} := by
    ext w
    change (F w.1 = w.2) ↔ _
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro e y
      have H := (reply_min hc hz w.1.val).2 y.val y.property
      simpa [F, ← e] using H
    · intro h
      apply Subtype.ext
      exact unique w.1.val (show w.1.val ≠
          0 from w.1.property) _ _ (reply_min hc hz _) ⟨w.2.property, fun y hy => h ⟨y, hy⟩⟩
  have cc : Continuous F := continuous_of_isClosed_graph (eq ▸ isClosed_iInter fun y =>
    isClosed_le (by fun_prop) (by fun_prop))
  apply measurable_of_continuousOn_compl_singleton 0
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp cc

variable {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]

/-- Measurability in both the tape and every real oracle reply on each finite
history length. Lists have most recent reply first. -/
def BorelRule (f : Ω → List E → V) : Prop := ∀ m : ℕ,
  Measurable (fun t : Ω × (Fin m → E) => f t.1 (List.ofFn t.2))

omit [NormedAddCommGroup E] in
theorem measurable_run (oracle : E → E) (ho : Measurable oracle)
    (ask : Ω → List E → E) (hq : BorelRule ask) (out : Ω → List E → V) (hf : BorelRule out)
    (t : ℕ) {m : ℕ} {hist : Ω → Fin m → E} (hh : Measurable hist) :
    Measurable (fun ω => out ω (play oracle (ask ω) t (List.ofFn (hist ω)))) := by
  induction t generalizing m with
  | zero => exact (hf m).comp (measurable_id.prodMk hh)
  | succ t ih =>
    let x := fun ω => oracle (ask ω (List.ofFn (hist ω)))
    have hx : Measurable x := ho.comp ((hq m).comp (measurable_id.prodMk hh))
    let h' : Ω → Fin (m + 1) → E := fun ω => Fin.cons (x ω) (hist ω)
    have hm : Measurable h' := by
      apply Measurable.of_eval; intro i; refine Fin.cases ?_ (fun j => ?_) i
      · simpa [h'] using hx
      · simpa [h', Function.comp_def] using (measurable_pi_apply j).comp hh
    have H := ih (hist := h') hm
    simpa [play, h', List.ofFn_succ, x] using H

end Lemmata.FrankWolfePS.Unique
