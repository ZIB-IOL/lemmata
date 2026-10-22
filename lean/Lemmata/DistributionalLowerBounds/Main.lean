module

public import Lemmata.DistributionalLowerBounds.Statement
public import Lemmata.DistributionalLowerBounds.Core.Distributional.OriginalModel

@[expose] public section

namespace Lemmata.DistributionalLowerBounds

-- DOCS_BEGIN_MAIN
/-- Main expectation and same-threshold probability bounds. -/
theorem distributional_lower_bounds : MainBounds :=
  Core.Distributional.original_model_lower_bounds

/-- Hard fixed instances, chosen before the independent random seed. -/
theorem fixed_instance_lower_bounds : FixedInstanceBounds :=
  Core.Distributional.original_model_fixed_instances

/-- First-return stopping-time tail; nontermination is included in the tail. -/
theorem stopping_time_lower_bound : StoppingTailBound :=
  Core.Distributional.original_model_stopping_tail
-- DOCS_END_MAIN

end Lemmata.DistributionalLowerBounds
