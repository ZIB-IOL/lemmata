module

public import Lemmata.ModifiedE8Bell.Envelope
public meta import Lemmata.ModifiedE8Bell.Statement

@[expose] public section
namespace Lemmata.ModifiedE8Bell
open scoped BigOperators

/-- The canonical-order attaining strategies, 1 = true = +1. -/
def witnessA (i : Setting) : Bool :=
  "010001011001101101111101110101100110111101111101100100111101110011111101010000001000000011101101111111111000010001101000".toList[i.val]?.getD '0' == '1'

def witnessB (i : Setting) : Bool :=
  "011101011001101111111101110101100110111101111001110110111101011011101101000000001000010011111101111111101000000011001000".toList[i.val]?.getD '0' == '1'

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem witness_value : fourBell witnessA witnessB = 24416 := by
  native_decide

def tournamentA (i : Setting) : Bool :=
  "111111111111111111110101101111110110111111101111111111111111111111111111111111111111111111111111111111111111111111111111".toList[i.val]?.getD '0' == '1'

def tournamentB (i : Setting) : Bool :=
  "111111111111110101011111110101011111010101110101100110101111111111111111111111111111111011111111111111111111111111111111".toList[i.val]?.getD '0' == '1'

set_option maxHeartbeats 0 in
theorem tournament_value : fourBell tournamentA tournamentB = 24416 := by native_decide

end Lemmata.ModifiedE8Bell
