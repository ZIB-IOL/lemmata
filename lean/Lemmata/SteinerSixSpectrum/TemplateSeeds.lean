module

public import Lemmata.SteinerSixSpectrum.Orbit

@[expose] public section

namespace Lemmata.SteinerSixSpectrum

-- The four orbit records used to obtain Wilson's row templates.
def design66 : OrbitRecord where
  order := 66
  maps := [[.value (1), .repeat 1 11, .value (-12), .value (14), .repeat 13 51, .value (13)],
    [.value (0), .value (3), .repeat 1 3, .value (-10), .repeat 4 7, .repeat 1 5, .repeat 13 8, .value (16), .repeat 26 25, .value (-36), .repeat 13 12, .value (29)]]
  starters := [[0, 1, 10, 17, 22, 24],
    [0, 2, 29, 30, 35, 46],
    [0, 13, 26, 39, 52, 65],
    [0, 15, 31, 34, 43, 49],
    [13, 14, 28, 37, 51, 56]]

def design91 : OrbitRecord where
  order := 91
  maps := [[.value (1), .repeat 1 89, .value (-90)],
    [.value (0), .value (74), .value (-17), .repeat 1 3, .repeat 5 10, .repeat 11 11, .repeat 16 64]]
  starters := [[0, 1, 28, 47, 80, 89]]

def incomplete81 : OrbitRecord where
  order := 81
  maps := [[.value (1), .value (1), .value (1), .value (-3), .value (5), .repeat 4 59, .value (4), .value (2), .value (-1), .value (3), .repeat 2 13],
    [.value (16), .value (3), .value (-1), .value (-1), .value (3), .repeat 4 3, .value (9), .repeat 7 3, .value (-5), .repeat 4 3, .value (-21), .repeat 8 7, .value (5), .repeat 24 7, .value (35), .repeat 32 31, .value (19), .value (5), .value (1), .value (1), .value (1), .value (-7), .repeat 4 3, .value (9), .repeat 8 7],
    [.value (53), .value (7), .value (-9), .value (7), .value (-3), .value (7), .value (-13), .value (7), .value (-4), .value (11), .value (-13), .repeat 8 4, .value (11), .value (-39), .repeat 8 7, .value (-4), .repeat 20 3, .value (-3), .repeat 28 3, .value (-17), .value (-5), .value (11), .value (-13), .value (9), .value (-5), .value (7), .value (-13), .value (8), .value (-1), .value (7), .repeat 8 4, .value (-9), .value (39), .repeat 4 3, .value (5), .repeat 12 3, .value (8), .repeat 24 7, .value (32), .value (14), .value (1), .value (-2), .value (3), .value (-11), .value (3), .value (-2), .value (1), .value (-3), .value (-3), .value (2), .value (-1), .value (9), .value (-1), .value (2), .value (-3)]]
  starters := [[0, 1, 24, 37, 43, 70],
    [0, 2, 4, 6, 64, 65]]

def incomplete106 : OrbitRecord where
  order := 106
  maps := [[.value (1), .repeat 1 5, .value (-6), .value (8), .repeat 7 76, .value (7), .value (2), .repeat 22 20]]
  starters := [[0, 1, 22, 41, 66, 96],
    [0, 2, 51, 60, 69, 90],
    [0, 3, 7, 46, 64, 97],
    [0, 8, 50, 55, 80, 92],
    [0, 9, 12, 23, 73, 89],
    [0, 10, 39, 56, 79, 102],
    [0, 13, 19, 28, 77, 99],
    [0, 14, 29, 52, 70, 103],
    [0, 15, 32, 45, 76, 105],
    [0, 16, 34, 61, 78, 85],
    [0, 17, 26, 31, 74, 101],
    [0, 18, 30, 38, 82, 98],
    [0, 20, 33, 63, 84, 87],
    [0, 24, 25, 62, 83, 104],
    [0, 27, 42, 54, 71, 91],
    [0, 35, 44, 48, 81, 100],
    [0, 36, 37, 53, 75, 86],
    [0, 47, 57, 59, 72, 93],
    [7, 8, 31, 45, 73, 90],
    [7, 9, 17, 50, 76, 88],
    [7, 14, 16, 22, 63, 95],
    [7, 18, 35, 57, 77, 94],
    [7, 19, 47, 48, 82, 96],
    [7, 23, 26, 32, 80, 104],
    [7, 24, 43, 53, 69, 93],
    [7, 27, 40, 56, 67, 85],
    [7, 28, 38, 59, 81, 92],
    [7, 33, 34, 52, 66, 102],
    [7, 37, 51, 62, 68, 105],
    [7, 39, 42, 58, 65, 103],
    [7, 41, 61, 70, 84, 101],
    [14, 15, 47, 62, 67, 87],
    [14, 17, 35, 53, 65, 92],
    [14, 21, 26, 36, 81, 89],
    [14, 24, 57, 58, 76, 91],
    [14, 25, 45, 49, 72, 102],
    [14, 37, 40, 48, 74, 99],
    [14, 51, 55, 56, 82, 100],
    [21, 28, 32, 60, 63, 98],
    [21, 29, 44, 53, 74, 96],
    [21, 31, 35, 37, 70, 93],
    [21, 39, 46, 54, 67, 90],
    [21, 42, 49, 56, 64, 104],
    [21, 45, 51, 77, 84, 92],
    [28, 30, 35, 47, 64, 90],
    [28, 37, 49, 50, 78, 91],
    [28, 44, 46, 57, 82, 85],
    [28, 55, 58, 61, 75, 93],
    [63, 64, 66, 70, 78, 105],
    [63, 71, 80, 81, 83, 85],
    [63, 72, 73, 75, 79, 92]]

end Lemmata.SteinerSixSpectrum
