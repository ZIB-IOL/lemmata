module

public import Lemmata.RM59.Proof.SimplexSearchChecks0
public import Lemmata.RM59.Proof.SimplexSearchChecks1
public import Lemmata.RM59.Proof.SimplexSearchChecks2
public import Lemmata.RM59.Proof.SimplexSearchChecks3

@[expose] public section

namespace Lemmata.RM59.SimplexSearchChecks

theorem chunks_checked (chunk : Fin 4) : chunkCheck chunk.val = true := by
  fin_cases chunk
  · exact chunk0_checked
  · exact chunk1_checked
  · exact chunk2_checked
  · exact chunk3_checked

end Lemmata.RM59.SimplexSearchChecks
