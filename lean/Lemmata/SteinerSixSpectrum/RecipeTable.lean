module

public import Lemmata.SteinerSixSpectrum.FiniteGluing

@[expose] public section

namespace Lemmata.SteinerSixSpectrum

inductive Recipe where
  | product (d m e : Nat) (delete : Bool)
  | groups (g u m e : Nat)
  | hole (h : Nat)
  | six (v h : Nat)
  | fibres (s t h : Nat)
  | sharedIncomplete (v h a : Nat) (mode : Puncture) (t m : Nat) (tail : List Nat)

-- Exceptional assemblies from the atlas and its C++ generator. Products and
-- uniform group inflations are found arithmetically.
set_option maxRecDepth 4096 in
def recipes : Array (Nat × Recipe) := #[
  (246, .hole 31),
  (276, .hole 31),
  (466, .sharedIncomplete 81 16 12 .array 0 0 []),
  (561, .fibres 18 5 26),
  (586, .sharedIncomplete 106 21 11 .axis 11 8 [8]),
  (601, .sharedIncomplete 106 21 14 .row 7 14 [1]),
  (616, .sharedIncomplete 106 21 17 .array 0 0 []),
  (651, .six 126 21),
  (661, .sharedIncomplete 131 26 1 .tail 7 15 [1]),
  (736, .sharedIncomplete 126 21 17 .three 0 0 [2, 0, 0]),
  (741, .sharedIncomplete 126 21 18 .three 0 0 [3, 0, 0]),
  (766, .sharedIncomplete 131 26 22 .three 0 0 [2, 2, 3]),
  (771, .sharedIncomplete 131 26 23 .three 0 0 [3, 3, 2]),
  (826, .sharedIncomplete 156 31 9 .row 16 7 [7, 15]),
  (861, .sharedIncomplete 156 31 16 .axis 16 8 [13]),
  (871, .sharedIncomplete 156 31 18 .row 8 17 [7]),
  (891, .six 166 21),
  (946, .six 171 16),
  (1021, .sharedIncomplete 171 16 15 .row 11 15 [5]),
  (1036, .sharedIncomplete 186 31 15 .row 11 15 [5]),
  (1051, .sharedIncomplete 186 31 18 .row 9 17 [5, 7, 8]),
  (1066, .sharedIncomplete 206 41 7 .tail 11 15 [7]),
  (1071, .six 196 21),
  (1096, .sharedIncomplete 206 41 13 .row 13 13 [9]),
  (1101, .sharedIncomplete 206 41 14 .row 13 13 [1, 9]),
  (1116, .sharedIncomplete 196 21 9 .tail 25 7 [9]),
  (1141, .sharedIncomplete 196 21 14 .row 13 14 [7]),
  (1146, .sharedIncomplete 196 21 15 .tail 25 7 [15]),
  (1161, .sharedIncomplete 196 21 18 .tail 25 7 [18]),
  (1186, .sharedIncomplete 211 31 15 .row 13 14 [13]),
  (1191, .sharedIncomplete 211 31 16 .tail 23 7 [16, 19]),
  (1221, .sharedIncomplete 211 31 22 .tail 23 7 [19, 22]),
  (1251, .six 226 21),
  (1396, .sharedIncomplete 246 31 15 .row 13 15 [5, 8, 11, 11]),
  (1411, .sharedIncomplete 246 31 18 .row 13 17 [1, 11]),
  (1486, .six 261 16),
  (1516, .sharedIncomplete 266 41 25 .tail 31 7 [8, 25]),
  (1546, .sharedIncomplete 276 31 9 .row 31 7 [8, 29])
]

end Lemmata.SteinerSixSpectrum
