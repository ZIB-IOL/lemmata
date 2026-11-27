module

public import Lemmata.FanoDiffusion.Proof
public import Lemmata.FanoDiffusion.Corollaries
public import Lemmata.FanoDiffusion.Renyi

@[expose] public section

namespace Lemmata.FanoDiffusion

-- DOCS_BEGIN_MAIN
/-- Proposition 2.1 for `α = 1`: the information diffusion Fano inequality for relative entropy. -/
theorem info_diffusion_fano_kl : InfoDiffusionFanoKL := Proof.info_diffusion_fano_kl

/-- Proposition 2.2: the Fano inequality for arbitrary relations along a Markov chain. -/
theorem fano_arbitrary_relation : FanoArbitraryRelation := Proof.fano_arbitrary_relation

/-- Corollary 2.6: the distance-based Fano inequality, mutual information version. -/
theorem distance_fano : DistanceFano := Proof.distance_fano

/-- Corollary 2.7: the continuous Fano inequality. -/
theorem continuous_fano : ContinuousFano := Proof.continuous_fano

/-- Proposition 2.1 for orders `α ≠ 1`, corrected: the normalized power `p^α/(p^α + (1 - p)^α)`. -/
theorem info_diffusion_fano_renyi : InfoDiffusionFanoRenyi := Proof.info_diffusion_fano_renyi

/-- Proposition 2.1 for orders `α > 1`, as stated in the paper. -/
theorem info_diffusion_fano_renyi_gt_one : InfoDiffusionFanoRenyiGtOne :=
  Proof.info_diffusion_fano_renyi_gt_one
-- DOCS_END_MAIN

end Lemmata.FanoDiffusion
