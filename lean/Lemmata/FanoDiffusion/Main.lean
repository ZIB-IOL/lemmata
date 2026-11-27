module

public import Lemmata.FanoDiffusion.Proof
public import Lemmata.FanoDiffusion.Corollaries

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
-- DOCS_END_MAIN

end Lemmata.FanoDiffusion
