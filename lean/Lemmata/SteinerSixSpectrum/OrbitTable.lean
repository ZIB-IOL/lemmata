module

public import Lemmata.SteinerSixSpectrum.TemplateSeeds

@[expose] public section

namespace Lemmata.SteinerSixSpectrum

-- Data from the S(2,6,n) orbit catalogue. Certificate verification is independent
-- of the classification and the orbit-development procedure used to obtain it.
set_option maxRecDepth 4096

def completeOrbits0 : OrbitRecord where
  order := 1
  maps := []
  starters := []

def completeOrbits1 : OrbitRecord where
  order := 6
  maps := []
  starters := [[0, 1, 2, 3, 4, 5]]

def completeOrbits2 : OrbitRecord where
  order := 31
  maps := [[.value (1), .repeat 1 29, .value (-30)]]
  starters := [[0, 1, 3, 8, 12, 18]]

def completeOrbits4 : OrbitRecord where
  order := 76
  maps := [[.value (1), .repeat 1 17, .value (-18), .value (20), .repeat 19 56],
    [.value (1), .value (11), .value (-8), .repeat 2 4, .repeat 5 10, .value (11), .value (-8), .value (29), .repeat 19 11, .repeat 7 8, .repeat 19 18, .value (-46), .repeat 19 18]]
  starters := [[0, 1, 37, 38, 48, 66],
    [0, 2, 5, 33, 41, 72],
    [0, 4, 13, 29, 46, 62],
    [0, 21, 43, 49, 50, 54],
    [19, 21, 53, 56, 61, 66],
    [19, 24, 43, 45, 62, 65]]

def completeOrbits6 : OrbitRecord where
  order := 96
  maps := [[.value (1), .repeat 1 46, .value (-47), .value (49), .repeat 48 47]]
  starters := [[0, 1, 21, 36, 46, 49],
    [0, 4, 41, 62, 64, 83],
    [0, 5, 34, 52, 59, 77],
    [0, 6, 80, 84, 93, 94],
    [0, 8, 16, 24, 32, 40],
    [0, 9, 31, 50, 53, 65],
    [0, 18, 55, 75, 81, 86],
    [48, 56, 64, 72, 80, 88]]

def completeOrbits7 : OrbitRecord where
  order := 106
  maps := [[.value (1), .repeat 1 51, .value (-52), .value (54), .repeat 53 52]]
  starters := [[0, 1, 16, 43, 51, 54],
    [0, 4, 63, 73, 80, 82],
    [0, 5, 33, 39, 72, 75],
    [0, 7, 31, 65, 97, 105],
    [0, 9, 41, 88, 102, 103],
    [0, 13, 36, 68, 84, 96],
    [0, 57, 77, 81, 99, 104]]

def completeOrbits8 : OrbitRecord where
  order := 111
  maps := [[.value (1), .repeat 1 35, .value (-36), .value (38), .repeat 37 73],
    [.value (37), .value (26), .value (-11), .value (-11), .repeat 3 6, .repeat 7 7, .repeat 10 21, .repeat 37 36, .value (-85), .repeat 37 36]]
  starters := [[0, 1, 21, 31, 35, 75],
    [0, 5, 49, 69, 88, 97],
    [0, 8, 38, 61, 101, 107],
    [0, 9, 60, 72, 82, 103],
    [0, 11, 56, 66, 79, 80],
    [0, 13, 54, 59, 89, 108],
    [0, 18, 52, 65, 85, 90]]

def completeOrbits9 : OrbitRecord where
  order := 121
  maps := [[.value (1), .repeat 1 9, .value (-10), .value (12), .repeat 11 109],
    [.value (11), .value (1), .repeat 1 108, .value (-120), .repeat 11 10]]
  starters := [[0, 1, 5, 81, 111, 120],
    [0, 3, 40, 55, 77, 101],
    [0, 14, 32, 71, 79, 104],
    [0, 16, 35, 67, 94, 103]]

def completeOrbits10 : OrbitRecord where
  order := 126
  maps := [[.value (1), .repeat 1 3, .value (-4), .value (6), .repeat 5 119, .value (5)],
    [.value (118), .value (-91), .value (56), .value (-77), .value (45), .value (46), .value (-77), .value (45), .value (42), .value (-66), .value (18), .value (62), .value (-91), .value (56), .value (-72), .value (35), .value (26), .value (-72), .value (70), .value (37), .value (-93), .repeat 14 3, .value (56), .value (25), .value (-77), .value (45), .value (-83), .value (59), .value (13), .value (-58), .value (34), .value (56), .value (-77), .value (35), .repeat 34 3, .value (-83), .value (32), .value (45), .value (-63), .value (34), .value (56), .value (-101), .value (64), .repeat 31 3, .value (17), .value (-83), .value (59), .value (-69), .value (48), .value (10), .value (-69), .value (53), .value (45), .value (-63), .value (7), .value (70), .value (-88), .value (64), .value (-99), .value (29), .repeat 14 3, .value (45), .value (-104), .value (48), .value (45), .value (-58), .value (34), .value (39), .value (-69), .value (48), .value (-80), .value (42), .value (32), .value (-80), .value (62), .value (34), .value (-69), .value (24), .value (64), .value (-99), .value (53), .value (-55), .value (21), .repeat 14 3, .value (59), .value (-112), .value (67), .value (34), .value (-69), .value (48), .value (36), .value (-80), .repeat 80 3, .value (24), .value (-91), .value (56), .value (48), .value (-80), .value (46), .repeat 20 3, .repeat 105 5, .value (53), .value (-90), .value (26), .value (53), .value (-55), .value (37), .value (40)]]
  starters := [[0, 1, 47, 55, 90, 99],
    [0, 8, 11, 19, 22, 125]]

def completeOrbits11 : OrbitRecord where
  order := 136
  maps := [[.value (5), .value (1), .repeat 1 8, .value (-14), .repeat 5 4, .value (16), .repeat 15 119, .value (11)],
    [.value (45), .value (1), .repeat 1 3, .value (34), .value (1), .value (-4), .value (1), .value (1), .value (-8), .repeat 4 3, .value (1), .value (-13), .repeat 15 4, .repeat 5 4, .value (-4), .value (39), .repeat 15 14, .value (-8), .repeat 4 3, .repeat 40 3, .repeat 45 43, .value (-86), .repeat 30 29, .value (-8), .repeat 70 4, .repeat 80 4, .repeat 15 6, .value (109)]]
  starters := [[0, 1, 2, 3, 4, 135],
    [0, 5, 10, 122, 127, 132],
    [0, 6, 26, 68, 75, 134],
    [0, 8, 18, 33, 76, 129],
    [0, 9, 43, 56, 99, 106],
    [0, 16, 70, 94, 102, 119]]

def completeOrbits12 : OrbitRecord where
  order := 141
  maps := [[.value (1), .repeat 1 33, .value (-34), .value (36), .repeat 35 104, .value (35)],
    [.value (17), .value (16), .value (-19), .repeat 2 9, .repeat 11 11, .repeat 13 12, .value (69), .repeat 25 12, .repeat 11 23, .repeat 35 34, .value (-68), .repeat 96 25, .repeat 11 9, .value (100)]]
  starters := [[0, 1, 49, 93, 99, 127],
    [0, 2, 20, 38, 39, 123],
    [0, 4, 62, 68, 115, 137],
    [0, 7, 14, 21, 28, 140],
    [0, 35, 52, 57, 73, 124],
    [0, 43, 66, 69, 74, 89],
    [35, 42, 49, 56, 63, 140],
    [35, 43, 59, 88, 105, 130]]

def completeOrbits13 : OrbitRecord where
  order := 151
  maps := [[.value (1), .repeat 1 149, .value (-150)]]
  starters := [[0, 1, 33, 36, 53, 96],
    [0, 2, 47, 81, 87, 112],
    [0, 4, 11, 23, 73, 94],
    [0, 5, 105, 114, 129, 143],
    [0, 10, 26, 54, 84, 102]]

def completeOrbits14 : OrbitRecord where
  order := 166
  maps := [[.value (5), .value (1), .repeat 1 4, .value (4), .value (-1), .value (-1), .value (-1), .value (-11), .repeat 5 4, .value (39), .value (23), .value (-7), .value (-2), .value (-7), .value (1), .value (-7), .value (23), .value (-7), .value (-7), .value (1), .value (-2), .value (-7), .value (18), .value (-2), .value (1), .value (-7), .value (-7), .value (-2), .value (18), .value (1), .repeat 19 3, .value (-2), .value (21), .repeat 25 24, .value (-54), .repeat 25 24, .value (96), .repeat 75 74, .value (71)],
    [.value (0), .value (3), .value (-2), .value (3), .value (-2), .value (5), .repeat 4 3, .value (3), .repeat 9 4, .value (3), .value (76), .repeat 6 4, .value (13), .repeat 5 4, .value (-12), .repeat 10 14, .value (24), .value (3), .value (-2), .value (-2), .value (3), .repeat 10 3, .value (-2), .value (3), .repeat 20 3, .repeat 10 12, .value (17), .repeat 45 19, .repeat 5 5, .value (-124), .repeat 4 3, .value (-2), .value (18), .repeat 5 4, .value (-7), .repeat 10 14, .value (35), .repeat 40 14, .repeat 55 10, .value (26), .repeat 40 14, .repeat 55 10, .value (85)]]
  starters := [[0, 1, 2, 3, 4, 165],
    [0, 5, 26, 34, 96, 110],
    [0, 15, 101, 105, 118, 135],
    [0, 40, 41, 42, 43, 44],
    [0, 50, 56, 72, 89, 156],
    [15, 16, 17, 18, 19, 165],
    [15, 24, 128, 134, 155, 160],
    [15, 40, 65, 93, 129, 158],
    [15, 47, 76, 99, 137, 145]]

def completeOrbits15 : OrbitRecord where
  order := 171
  maps := [[.value (19), .value (7), .value (7), .value (-12), .repeat 3 7, .repeat 8 8, .repeat 1 3, .repeat 19 16, .value (-50), .repeat 19 18, .value (64), .repeat 57 113],
    [.value (57), .value (1), .repeat 1 17, .value (18), .value (1), .value (-18), .repeat 19 16, .value (6), .repeat 16 15, .repeat 33 3, .value (17), .repeat 57 56, .value (-153), .repeat 56 17, .value (-18), .value (24), .repeat 36 16, .value (1), .value (1), .value (29), .repeat 10 9, .repeat 1 9]]
  starters := [[0, 1, 58, 99, 158, 168],
    [0, 2, 9, 64, 79, 112],
    [0, 3, 31, 33, 39, 53],
    [0, 4, 52, 78, 114, 144],
    [0, 5, 59, 86, 105, 126],
    [0, 8, 32, 80, 143, 164],
    [0, 20, 46, 69, 85, 102]]

def completeOrbits16 : OrbitRecord where
  order := 181
  maps := [[.value (1), .repeat 1 179, .value (-180)]]
  starters := [[0, 1, 79, 112, 124, 133],
    [0, 2, 27, 67, 110, 152],
    [0, 3, 10, 47, 131, 165],
    [0, 4, 55, 66, 146, 161],
    [0, 5, 28, 92, 109, 168],
    [0, 6, 38, 99, 151, 173]]

def completeOrbits17 : OrbitRecord where
  order := 196
  maps := [[.value (1), .repeat 1 47, .value (-48), .value (50), .repeat 49 146],
    [.value (0), .value (30), .value (-19), .value (30), .value (-19), .repeat 3 3, .repeat 5 10, .repeat 13 13, .repeat 18 18, .value (79), .repeat 49 48, .value (30), .repeat 49 48, .value (-117), .repeat 49 48]]
  starters := [[0, 1, 35, 38, 136, 175],
    [0, 4, 69, 122, 148, 155],
    [0, 6, 51, 74, 102, 133],
    [0, 50, 77, 86, 111, 140],
    [0, 52, 67, 124, 131, 167],
    [0, 53, 73, 158, 163, 166],
    [0, 58, 60, 64, 97, 106],
    [0, 59, 83, 90, 126, 153],
    [49, 50, 99, 118, 148, 179],
    [49, 60, 122, 135, 167, 169]]

def completeOrbits18 : OrbitRecord where
  order := 201
  maps := [[.value (1), .repeat 1 65, .value (-66), .value (68), .repeat 67 133],
    [.value (1), .value (37), .value (-30), .repeat 2 8, .repeat 9 36, .repeat 20 21, .repeat 67 133]]
  starters := [[0, 1, 140, 168, 193, 198],
    [0, 2, 101, 122, 133, 178],
    [0, 3, 48, 83, 164, 191],
    [0, 4, 40, 73, 76, 169],
    [0, 5, 55, 98, 116, 163],
    [0, 67, 68, 96, 104, 134],
    [67, 69, 121, 154, 176, 195],
    [67, 84, 110, 162, 182, 185]]

def completeOrbits19 : OrbitRecord where
  order := 216
  maps := [[.value (1), .repeat 1 41, .value (-42), .value (44), .repeat 43 171, .value (43)],
    [.value (43), .value (1), .repeat 1 170, .value (-214), .repeat 43 42, .value (173)],
    [.value (0), .value (6), .repeat 1 6, .value (-37), .repeat 7 34, .repeat 1 8, .repeat 43 165]]
  starters := [[0, 1, 5, 11, 28, 35],
    [0, 2, 48, 112, 165, 176],
    [0, 3, 70, 99, 143, 181],
    [0, 43, 86, 129, 172, 215]]

def completeOrbits20 : OrbitRecord where
  order := 226
  maps := [[.value (75), .value (23), .value (-7), .value (-2), .value (-7), .value (1), .value (-7), .value (23), .value (-7), .value (-7), .value (1), .value (-2), .value (-7), .value (18), .value (-2), .value (1), .value (-7), .value (-7), .value (-2), .value (18), .value (1), .repeat 19 3, .value (-2), .value (40), .repeat 10 9, .value (-4), .repeat 35 14, .value (15), .repeat 45 19, .repeat 35 5, .value (18), .repeat 75 74, .value (-207), .repeat 75 74, .value (168)],
    [.value (52), .value (-2), .value (3), .value (-2), .value (3), .value (13), .repeat 5 4, .value (-12), .repeat 10 14, .value (-39), .repeat 4 3, .value (-2), .value (13), .repeat 5 4, .value (-12), .repeat 10 14, .value (-34), .repeat 4 3, .value (-2), .value (18), .repeat 5 4, .value (-7), .repeat 10 14, .value (112), .repeat 60 9, .repeat 75 15, .value (-14), .repeat 60 9, .repeat 75 15, .value (65), .repeat 50 24, .value (16), .repeat 125 24, .value (40), .repeat 175 49, .value (38)]]
  starters := [[0, 1, 50, 53, 140, 151],
    [0, 5, 10, 15, 20, 225],
    [0, 6, 69, 166, 190, 193],
    [0, 8, 62, 73, 80, 108],
    [0, 9, 78, 88, 162, 173],
    [0, 32, 117, 125, 171, 211],
    [0, 33, 101, 132, 154, 213]]

def completeOrbits21 : OrbitRecord where
  order := 241
  maps := [[.value (1), .repeat 1 239, .value (-240)]]
  starters := [[0, 1, 7, 136, 151, 232],
    [0, 2, 20, 182, 212, 229],
    [0, 3, 8, 56, 124, 169],
    [0, 4, 40, 123, 183, 217],
    [0, 11, 50, 77, 142, 215],
    [0, 13, 38, 84, 139, 172],
    [0, 19, 70, 133, 174, 218],
    [0, 21, 43, 95, 130, 184]]

def completeOrbits22 : OrbitRecord where
  order := 261
  maps := [[.value (1), .repeat 1 11, .value (-12), .value (14), .repeat 13 246, .value (13)],
    [.value (13), .value (1), .repeat 1 50, .value (-64), .repeat 13 12, .value (66), .repeat 65 194, .value (53)],
    [.value (1), .value (9), .value (-4), .value (-4), .repeat 3 6, .repeat 4 3, .value (9), .repeat 13 51, .value (73), .repeat 13 9, .repeat 3 4, .repeat 13 116, .value (-186), .repeat 65 64, .value (139)]]
  starters := [[0, 1, 73, 105, 168, 216],
    [0, 2, 69, 160, 165, 259],
    [0, 13, 26, 39, 52, 260],
    [0, 14, 89, 133, 226, 246],
    [0, 15, 68, 172, 194, 214],
    [0, 17, 48, 173, 252, 256],
    [0, 20, 65, 83, 185, 210],
    [0, 27, 180, 220, 238, 249],
    [0, 33, 70, 125, 242, 254],
    [65, 66, 70, 85, 94, 153],
    [65, 71, 138, 140, 197, 202],
    [65, 78, 91, 104, 117, 260],
    [65, 81, 108, 179, 216, 244],
    [65, 90, 107, 154, 186, 229]]

def completeOrbits23 : OrbitRecord where
  order := 271
  maps := [[.value (1), .repeat 1 269, .value (-270)]]
  starters := [[0, 1, 19, 233, 243, 263],
    [0, 2, 6, 62, 116, 174],
    [0, 3, 44, 105, 128, 192],
    [0, 5, 45, 145, 181, 195],
    [0, 7, 118, 177, 193, 245],
    [0, 11, 130, 165, 178, 202],
    [0, 12, 55, 77, 108, 197],
    [0, 15, 98, 147, 220, 254],
    [0, 21, 63, 109, 134, 201]]

def completeOrbits24 : OrbitRecord where
  order := 286
  maps := [[.value (19), .value (1), .repeat 1 74, .value (-79), .repeat 4 3, .value (-18), .repeat 19 14, .value (100), .repeat 95 189, .value (81)],
    [.value (11), .value (-8), .repeat 2 4, .repeat 5 5, .repeat 7 7, .value (-8), .value (22), .repeat 18 17, .value (11), .value (22), .repeat 18 17, .repeat 38 4, .repeat 18 15, .repeat 38 3, .repeat 18 16, .value (-8), .value (24), .repeat 95 189, .value (13)]]
  starters := [[0, 1, 12, 81, 112, 223],
    [0, 2, 16, 230, 231, 242],
    [0, 4, 10, 259, 262, 264],
    [0, 20, 64, 96, 184, 246],
    [0, 21, 62, 189, 256, 282],
    [0, 23, 124, 163, 193, 210],
    [0, 24, 66, 105, 122, 243],
    [0, 26, 129, 151, 186, 201],
    [0, 35, 51, 67, 83, 285],
    [0, 95, 135, 139, 145, 190],
    [0, 141, 148, 149, 162, 225],
    [0, 146, 153, 156, 158, 273],
    [0, 172, 200, 224, 253, 278],
    [0, 178, 198, 202, 208, 257],
    [95, 119, 156, 194, 213, 254],
    [95, 130, 146, 162, 178, 285],
    [190, 225, 241, 257, 273, 285]]

def completeOrbits25 : OrbitRecord where
  order := 291
  maps := [[.value (1), .repeat 1 95, .value (-96), .value (98), .repeat 97 193],
    [.value (78), .value (-36), .value (-36), .value (61), .repeat 2 3, .repeat 3 6, .repeat 8 8, .repeat 19 19, .repeat 35 43, .repeat 19 14, .value (158), .repeat 97 193]]
  starters := [[0, 1, 45, 79, 193, 265],
    [0, 2, 109, 147, 155, 197],
    [0, 3, 119, 166, 236, 269],
    [0, 4, 20, 141, 252, 290],
    [0, 7, 64, 105, 186, 267],
    [0, 10, 208, 214, 216, 261],
    [0, 13, 30, 157, 181, 190],
    [0, 97, 194, 212, 225, 242],
    [0, 102, 103, 120, 185, 262],
    [0, 123, 149, 239, 259, 274],
    [97, 99, 120, 220, 278, 283]]

def completeOrbits26 : OrbitRecord where
  order := 301
  maps := [[.value (1), .repeat 1 299, .value (-300)]]
  starters := [[0, 1, 15, 218, 237, 298],
    [0, 2, 32, 38, 173, 181],
    [0, 5, 75, 100, 174, 194],
    [0, 7, 29, 46, 191, 259],
    [0, 9, 66, 106, 118, 256],
    [0, 10, 69, 113, 146, 209],
    [0, 11, 125, 211, 254, 278],
    [0, 13, 73, 89, 210, 266],
    [0, 21, 93, 144, 175, 260],
    [0, 26, 159, 196, 246, 274]]

def completeOrbits27 : OrbitRecord where
  order := 306
  maps := [[.value (1), .repeat 1 59, .value (-60), .value (62), .repeat 61 243, .value (61)],
    [.value (61), .value (1), .repeat 1 242, .value (-304), .repeat 61 60, .value (245)],
    [.value (0), .value (3), .repeat 1 19, .value (-58), .repeat 20 39, .repeat 1 21, .repeat 61 224]]
  starters := [[0, 1, 145, 161, 269, 281],
    [0, 2, 78, 107, 264, 287],
    [0, 61, 122, 183, 244, 305]]

def completeOrbits28 : OrbitRecord where
  order := 316
  maps := [[.value (35), .value (1), .repeat 1 68, .value (-97), .repeat 28 27, .value (-28), .value (-6), .repeat 7 5, .value (135), .repeat 105 209, .value (100)],
    [.value (105), .value (4), .value (-3), .repeat 2 4, .value (9), .repeat 4 3, .repeat 7 7, .repeat 2 3, .value (2), .repeat 6 4, .value (-3), .value (4), .value (9), .repeat 19 4, .repeat 21 8, .value (-3), .value (9), .repeat 34 5, .repeat 28 6, .repeat 49 51, .value (4), .repeat 105 104, .value (-278), .repeat 49 6, .value (-27), .repeat 70 27, .value (38), .repeat 28 6, .value (-27), .repeat 70 27, .value (45), .repeat 28 6, .value (-27), .repeat 119 27, .value (224)],
    [.value (6), .value (-1), .repeat 1 5, .value (12), .repeat 6 5, .value (6), .value (5), .repeat 6 5, .value (-1), .repeat 7 4, .repeat 25 3, .repeat 7 3, .repeat 31 4, .value (64), .repeat 21 13, .value (-31), .repeat 20 5, .value (-1), .value (5), .repeat 57 6, .repeat 56 6, .value (-1), .value (-34), .repeat 21 20, .value (-24), .repeat 56 13, .value (61), .repeat 77 6, .value (5), .repeat 42 20, .repeat 126 7, .value (57), .repeat 63 27, .repeat 140 7, .value (-34), .repeat 21 20, .value (-31), .repeat 56 13, .value (63), .repeat 91 20, .repeat 217 14, .repeat 210 5, .repeat 21 9, .value (-31), .repeat 154 20, .repeat 105 3, .repeat 21 18, .repeat 147 5, .repeat 56 9, .value (58)]]
  starters := [[0, 1, 45, 100, 107, 221],
    [0, 2, 24, 168, 194, 228],
    [0, 3, 31, 160, 177, 222],
    [0, 7, 57, 63, 197, 301],
    [0, 9, 124, 130, 210, 238],
    [0, 10, 20, 23, 33, 315],
    [0, 15, 53, 85, 135, 249],
    [0, 16, 74, 152, 183, 278],
    [0, 36, 82, 138, 162, 180],
    [0, 55, 112, 201, 264, 311]]

def completeOrbits29 : OrbitRecord where
  order := 321
  maps := [[.value (7), .value (1), .repeat 1 26, .value (-29), .value (1), .value (-6), .repeat 7 4, .value (38), .repeat 35 279, .value (32), .repeat 4 3, .value (-4), .value (5)],
    [.value (35), .value (1), .repeat 1 68, .value (-104), .repeat 35 34, .value (106), .repeat 105 209, .value (71), .repeat 6 5],
    [.value (105), .value (2), .value (2), .value (2), .value (-5), .value (2), .value (2), .value (3), .repeat 6 5, .repeat 7 7, .value (-5), .value (10), .repeat 13 5, .repeat 7 6, .value (-5), .value (2), .value (5), .repeat 35 174, .value (-310), .repeat 105 104, .value (215), .value (1), .repeat 1 4],
    [.value (0), .value (6), .value (-1), .repeat 1 4, .value (29), .value (-1), .value (-1), .repeat 9 4, .value (-8), .repeat 7 20, .value (25), .repeat 35 280, .value (4), .repeat 5 3, .value (4)]]
  starters := [[0, 1, 39, 248, 250, 284],
    [0, 2, 108, 111, 214, 215],
    [0, 7, 143, 151, 282, 292],
    [0, 8, 120, 135, 271, 318],
    [0, 9, 85, 101, 128, 163],
    [0, 10, 87, 100, 124, 133],
    [0, 11, 59, 199, 264, 274],
    [0, 12, 91, 262, 277, 301],
    [0, 13, 19, 25, 31, 320],
    [0, 36, 104, 122, 231, 254],
    [0, 43, 136, 224, 246, 303]]

def completeOrbits30 : OrbitRecord where
  order := 336
  maps := [[.value (1), .repeat 1 59, .value (-60), .value (62), .repeat 61 243, .value (61), .repeat 32 30],
    [.value (61), .value (1), .repeat 1 242, .value (-304), .repeat 61 60, .value (246), .repeat 4 3, .value (-4), .value (6), .repeat 5 24, .value (5)]]
  starters := [[0, 1, 68, 137, 214, 271],
    [0, 2, 15, 34, 144, 147],
    [0, 4, 9, 45, 188, 200],
    [0, 6, 37, 44, 284, 294],
    [0, 8, 26, 47, 71, 99],
    [0, 11, 90, 141, 239, 280],
    [0, 61, 122, 183, 244, 335],
    [0, 62, 165, 193, 259, 315],
    [0, 64, 140, 189, 273, 322],
    [0, 70, 123, 231, 251, 305],
    [0, 74, 154, 185, 272, 325],
    [0, 75, 158, 218, 261, 331],
    [0, 100, 156, 206, 246, 313]]

def completeOrbits31 : OrbitRecord where
  order := 346
  maps := [[.value (1), .repeat 1 5, .value (-6), .value (8), .repeat 7 307, .value (7), .repeat 316 6, .repeat 1 24],
    [.value (35), .value (4), .value (-3), .repeat 2 4, .value (7), .repeat 6 5, .value (4), .value (7), .value (-3), .repeat 14 6, .value (4), .repeat 8 5, .repeat 21 4, .repeat 3 3, .value (6), .repeat 35 34, .value (-74), .repeat 20 5, .repeat 21 4, .repeat 2 4, .value (-30), .repeat 13 5, .repeat 28 5, .repeat 21 10, .value (123), .repeat 105 209, .value (89), .value (1), .value (1), .value (1), .value (-4), .value (6), .repeat 5 24, .value (5)],
    [.value (105), .value (1), .repeat 1 208, .value (-289), .value (1), .value (1), .value (-6), .repeat 7 3, .value (8), .repeat 7 6, .value (-29), .repeat 19 4, .value (-6), .repeat 14 4, .repeat 7 11, .value (45), .repeat 35 69, .value (231), .repeat 6 3, .value (-4), .value (6), .repeat 5 24, .value (5)]]
  starters := [[0, 1, 164, 263, 265, 292],
    [0, 2, 35, 142, 266, 310],
    [0, 7, 37, 45, 58, 158],
    [0, 8, 42, 181, 254, 325],
    [0, 9, 71, 130, 247, 340],
    [0, 11, 75, 180, 255, 330],
    [0, 12, 72, 107, 122, 211],
    [0, 13, 19, 25, 31, 345],
    [0, 16, 59, 176, 244, 339],
    [0, 17, 141, 167, 289, 304],
    [0, 18, 57, 119, 223, 252],
    [0, 39, 124, 258, 305, 320],
    [0, 44, 218, 267, 283, 318],
    [0, 48, 114, 190, 259, 307],
    [0, 63, 94, 221, 248, 313],
    [0, 65, 97, 131, 155, 185]]

def completeOrbits32 : OrbitRecord where
  order := 351
  maps := [[.value (1), .repeat 1 11, .value (-12), .value (14), .repeat 13 337],
    [.value (39), .value (1), .repeat 1 76, .value (-116), .repeat 39 38, .value (118), .repeat 117 233],
    [.value (117), .value (1), .repeat 1 232, .value (-350), .repeat 117 116],
    [.value (36), .value (-3), .value (-3), .value (-3), .value (10), .repeat 4 7, .value (-3), .value (-14), .repeat 5 4, .repeat 14 8, .value (15), .repeat 24 10, .value (10), .value (-3), .value (55), .repeat 39 311]]
  starters := [[0, 1, 14, 18, 27, 37],
    [0, 2, 118, 140, 340, 349],
    [0, 4, 24, 63, 219, 314],
    [0, 5, 48, 112, 282, 330],
    [0, 6, 149, 154, 247, 258],
    [0, 15, 133, 238, 275, 321],
    [0, 19, 51, 202, 263, 332],
    [0, 21, 42, 128, 212, 331],
    [0, 52, 111, 147, 176, 205]]

def completeOrbits33 : OrbitRecord where
  order := 361
  maps := [[.value (1), .repeat 1 17, .value (-18), .value (20), .repeat 19 341],
    [.value (19), .value (1), .repeat 1 340, .value (-360), .repeat 19 18]]
  starters := [[0, 1, 12, 41, 72, 280],
    [0, 2, 5, 82, 125, 180],
    [0, 4, 13, 24, 134, 220],
    [0, 19, 47, 108, 241, 256],
    [0, 21, 104, 182, 233, 348],
    [0, 22, 118, 199, 245, 311],
    [0, 23, 73, 132, 292, 328],
    [0, 25, 144, 162, 188, 235],
    [0, 27, 57, 122, 286, 324],
    [0, 29, 45, 87, 150, 234],
    [0, 33, 76, 169, 204, 283],
    [0, 36, 84, 191, 290, 329]]

def completeOrbits34 : OrbitRecord where
  order := 366
  maps := [[.value (1), .repeat 1 71, .value (-72), .value (74), .repeat 73 291, .value (73)],
    [.value (200), .value (8), .value (8), .value (-65), .value (8), .repeat 1 7, .repeat 9 45, .repeat 19 16, .value (81), .repeat 73 145, .value (-284), .repeat 146 145, .value (246)]]
  starters := [[0, 1, 92, 128, 246, 266],
    [0, 2, 158, 209, 251, 262],
    [0, 3, 238, 276, 300, 360],
    [0, 5, 85, 139, 180, 190],
    [0, 73, 146, 219, 292, 365]]

def completeOrbits35 : OrbitRecord where
  order := 376
  maps := [[.value (125), .value (48), .value (12), .value (36), .value (5), .value (6), .value (-101), .value (23), .value (37), .value (11), .value (6), .value (30), .value (-101), .value (18), .value (42), .value (-19), .value (36), .repeat 6 3, .value (6), .value (17), .value (31), .value (30), .value (-96), .value (-13), .value (17), .value (36), .value (30), .value (24), .value (6), .value (-107), .repeat 11 3, .value (-19), .value (24), .value (-77), .value (12), .value (36), .value (-19), .value (30), .value (24), .value (-102), .value (37), .value (6), .value (11), .value (30), .value (24), .value (-107), .value (17), .repeat 5 3, .value (18), .value (6), .value (-108), .repeat 30 4, .value (18), .value (-108), .repeat 30 4, .value (48), .value (-113), .repeat 30 4, .value (23), .value (-88), .value (-8), .repeat 24 3, .value (42), .value (-19), .value (-89), .repeat 30 4, .value (17), .value (-94), .value (30), .value (29), .value (-24), .value (48), .value (12), .value (-89), .value (5), .value (6), .value (24), .value (23), .value (37), .value (-114), .value (17), .value (24), .value (18), .value (17), .value (36), .value (1), .value (-95), .value (29), .value (18), .value (17), .value (1), .value (36), .value (-120), .value (24), .value (48), .value (-19), .value (37), .value (11), .value (-95), .repeat 60 3, .value (42), .value (11), .value (-95), .value (112), .repeat 125 124, .value (-245), .repeat 24 3, .value (30), .value (1), .value (-96), .value (18), .value (17), .value (31), .value (6), .value (5), .value (-101), .value (48), .value (12), .repeat 95 3, .value (-101), .value (23), .value (1), .value (42), .repeat 6 3, .value (-8), .value (37), .repeat 101 3, .value (6), .value (-107), .repeat 11 3, .value (6), .repeat 113 3, .value (36), .value (1), .value (30), .value (29), .value (-107), .repeat 60 3, .value (5), .value (24), .value (-77), .value (-13), .repeat 5 3, .value (48), .value (-19), .value (-88), .repeat 30 4, .value (18), .value (-83), .repeat 30 4, .value (18), .value (-108), .repeat 30 4, .value (18), .value (-108), .value (12), .repeat 24 3, .value (12), .value (6), .value (-114), .repeat 136 3, .value (1), .value (42), .repeat 6 3, .value (6), .value (18), .value (17), .value (-89), .value (30), .value (1), .repeat 114 3, .value (-94), .value (-8), .repeat 130 3, .value (11), .value (6), .value (-95), .repeat 155 4, .value (36), .repeat 6 3, .repeat 220 3, .value (-95), .repeat 155 4, .value (36), .value (-120), .value (374)],
    [.value (25), .value (3), .value (-2), .value (3), .value (-2), .value (19), .value (3), .value (-2), .value (-2), .value (3), .value (-6), .repeat 9 3, .repeat 5 5, .value (-2), .value (-1), .repeat 14 3, .value (-2), .value (69), .repeat 25 24, .value (-56), .repeat 25 49, .repeat 75 25, .value (74), .repeat 25 4, .value (-6), .repeat 25 4, .value (19), .repeat 25 14, .value (81), .repeat 15 14, .repeat 35 3, .repeat 65 7, .value (-69), .repeat 15 4, .repeat 10 3, .repeat 55 7, .repeat 80 10, .value (-44), .repeat 15 14, .value (24), .repeat 55 9, .repeat 75 4, .repeat 70 11, .repeat 55 10, .value (70), .repeat 20 19, .repeat 60 5, .value (99), .repeat 25 24, .value (-26), .repeat 50 74, .value (75)]]
  starters := [[0, 1, 76, 96, 107, 313],
    [0, 2, 13, 22, 140, 330],
    [0, 6, 12, 18, 24, 375],
    [0, 26, 209, 261, 276, 315],
    [0, 28, 70, 170, 256, 326],
    [0, 30, 176, 207, 364, 366],
    [0, 33, 152, 249, 296, 351],
    [0, 39, 197, 237, 253, 305]]

def completeOrbits36 : OrbitRecord where
  order := 406
  maps := [[.value (81), .value (27), .value (27), .value (-45), .repeat 3 5, .value (-71), .repeat 9 17, .value (6), .value (-54), .value (27), .value (9), .value (-54), .value (27), .value (36), .value (-54), .value (27), .value (34), .repeat 9 8, .value (37), .repeat 9 8, .value (-3), .value (27), .value (-54), .value (36), .value (27), .value (-54), .value (9), .value (27), .value (-54), .value (37), .repeat 9 8, .value (34), .repeat 9 8, .value (78), .repeat 81 242, .value (-327), .repeat 81 80, .value (402)],
    [.value (0), .value (1), .value (1), .value (25), .repeat 3 5, .value (-53), .repeat 9 17, .value (18), .value (-2), .value (1), .value (-53), .value (-2), .value (1), .value (28), .value (-2), .value (1), .value (22), .repeat 9 8, .value (31), .repeat 9 8, .value (-9), .value (1), .value (-2), .value (28), .value (1), .value (-2), .value (-53), .value (1), .value (-2), .value (31), .repeat 9 8, .value (22), .repeat 9 8, .value (231), .value (1), .value (1), .value (-56), .repeat 63 5, .value (19), .repeat 9 8, .value (28), .repeat 9 8, .value (-9), .repeat 60 5, .repeat 66 3, .repeat 72 3, .repeat 9 6, .repeat 90 3, .repeat 9 6, .repeat 81 6, .repeat 3 3, .value (-50), .repeat 9 17, .value (152), .repeat 54 53, .value (-9), .repeat 135 26, .value (-216), .repeat 207 17, .repeat 225 9, .value (18), .repeat 216 17, .repeat 9 9, .repeat 81 3, .repeat 279 6, .value (-62), .repeat 297 17, .value (102), .repeat 60 5, .repeat 3 3, .value (-59), .repeat 9 8, .value (-50), .repeat 9 8, .repeat 81 3, .repeat 60 3, .repeat 66 3, .repeat 72 3, .repeat 9 6, .repeat 297 3, .repeat 9 6, .repeat 81 6, .repeat 147 3, .value (28), .repeat 9 17, .value (145)]]
  starters := [[0, 1, 113, 229, 249, 325],
    [0, 3, 189, 233, 341, 395],
    [0, 4, 191, 221, 362, 398],
    [0, 5, 82, 153, 263, 306],
    [0, 15, 87, 121, 295, 308],
    [0, 16, 23, 357, 364, 371],
    [0, 38, 101, 166, 312, 329],
    [0, 143, 216, 252, 384, 405]]

def completeOrbits37 : OrbitRecord where
  order := 411
  maps := [[.value (81), .value (33), .value (24), .value (-3), .value (-48), .value (24), .value (-3), .value (33), .value (-57), .value (35), .value (33), .value (-57), .value (-3), .repeat 12 5, .value (32), .repeat 15 5, .repeat 12 3, .value (-26), .value (24), .value (-48), .value (-3), .value (24), .value (33), .value (-3), .value (-57), .value (33), .value (5), .value (-57), .value (33), .value (-3), .repeat 12 5, .value (-49), .repeat 15 5, .repeat 12 3, .value (55), .value (-57), .value (24), .value (6), .value (24), .value (-57), .value (6), .value (24), .value (24), .value (-40), .value (24), .value (24), .value (6), .repeat 12 5, .value (17), .repeat 15 5, .repeat 12 3, .value (52), .repeat 81 242, .value (-353), .repeat 81 80, .value (376), .value (1), .repeat 1 4],
    [.value (0), .value (1), .value (1), .value (7), .repeat 3 5, .value (-12), .value (-2), .value (1), .value (10), .repeat 3 5, .value (-21), .value (1), .value (-2), .value (10), .repeat 3 5, .value (38), .repeat 18 17, .value (-12), .repeat 45 8, .value (-46), .repeat 18 8, .value (-21), .repeat 18 8, .value (-21), .repeat 45 8, .value (191), .value (1), .value (1), .value (-20), .repeat 18 5, .value (6), .value (-2), .value (1), .value (-17), .repeat 18 5, .value (15), .value (1), .value (-2), .value (-17), .repeat 45 5, .value (-16), .repeat 18 8, .value (6), .repeat 18 8, .value (6), .repeat 45 8, .value (-19), .repeat 18 8, .value (15), .repeat 63 17, .value (227), .repeat 18 17, .repeat 63 9, .repeat 81 9, .repeat 99 9, .repeat 81 18, .repeat 18 9, .value (15), .repeat 45 8, .value (-228), .repeat 189 17, .repeat 252 9, .value (-46), .repeat 207 17, .repeat 270 18, .value (-12), .repeat 63 17, .value (112), .repeat 324 26, .value (-43), .repeat 324 26, .value (35), .repeat 324 26, .value (90), .value (-1), .value (3), .value (-1), .value (2), .value (1)]]
  starters := [[0, 1, 88, 229, 271, 325],
    [0, 3, 8, 30, 41, 48],
    [0, 12, 25, 70, 120, 351],
    [0, 28, 150, 174, 287, 343],
    [0, 31, 62, 97, 119, 147],
    [0, 32, 122, 207, 285, 391],
    [0, 84, 219, 280, 328, 410],
    [0, 92, 184, 303, 348, 407],
    [0, 106, 203, 266, 335, 405],
    [0, 110, 214, 254, 364, 409]]

def completeOrbits38 : OrbitRecord where
  order := 421
  maps := [[.value (1), .repeat 1 419, .value (-420)]]
  starters := [[0, 1, 80, 100, 396, 417],
    [0, 2, 10, 221, 261, 389],
    [0, 3, 169, 243, 361, 373],
    [0, 6, 59, 179, 271, 397],
    [0, 7, 119, 146, 286, 393],
    [0, 9, 67, 103, 299, 344],
    [0, 11, 55, 163, 245, 383],
    [0, 13, 171, 236, 332, 384],
    [0, 14, 71, 141, 207, 298],
    [0, 15, 124, 237, 315, 390],
    [0, 16, 33, 101, 165, 340],
    [0, 18, 61, 133, 172, 195],
    [0, 19, 73, 129, 216, 399],
    [0, 29, 117, 215, 305, 374]]

def completeOrbits39 : OrbitRecord where
  order := 436
  maps := [[.value (81), .value (33), .value (24), .value (-27), .value (24), .value (-48), .value (54), .value (-57), .value (24), .value (43), .value (-57), .value (24), .value (-27), .repeat 12 5, .value (34), .repeat 15 5, .repeat 12 3, .value (-60), .value (24), .repeat 6 3, .value (-57), .value (54), .value (-57), .value (33), .value (31), .value (-57), .value (33), .value (-27), .repeat 12 5, .value (7), .repeat 15 5, .repeat 12 3, .value (-33), .value (24), .repeat 6 3, .value (-57), .value (54), .value (-48), .value (24), .value (7), .value (-48), .repeat 51 3, .repeat 12 4, .value (40), .repeat 15 5, .repeat 12 3, .value (12), .repeat 81 242, .value (-393), .repeat 81 80, .value (336), .value (1), .repeat 1 29],
    [.value (0), .value (1), .value (1), .value (7), .repeat 3 5, .value (-13), .value (1), .value (-2), .value (10), .repeat 3 5, .value (-19), .value (-2), .value (1), .value (10), .repeat 3 5, .value (55), .value (-2), .value (1), .value (-17), .repeat 9 5, .value (5), .value (1), .value (1), .value (-20), .repeat 36 5, .value (14), .value (1), .value (-2), .value (-17), .repeat 36 5, .value (-26), .repeat 6 5, .repeat 12 3, .value (8), .repeat 33 5, .repeat 39 3, .value (5), .repeat 33 5, .repeat 39 3, .value (184), .repeat 45 8, .value (5), .repeat 45 8, .repeat 36 3, .repeat 72 6, .value (-26), .repeat 45 8, .value (14), .repeat 45 8, .repeat 36 3, .repeat 72 6, .value (55), .repeat 126 17, .value (-13), .repeat 153 8, .value (127), .repeat 126 17, .repeat 81 18, .repeat 126 9, .repeat 36 3, .repeat 81 24, .value (-22), .repeat 81 8, .value (-261), .repeat 99 17, .value (-22), .repeat 45 8, .repeat 216 3, .repeat 99 15, .value (14), .repeat 126 8, .value (-29), .repeat 180 17, .repeat 252 9, .value (221), .repeat 72 17, .repeat 117 9, .repeat 162 3, .repeat 72 15, .repeat 279 9, .repeat 324 18, .repeat 279 9, .value (155), .value (-1), .value (3), .value (-1), .value (4), .value (1), .value (-2), .value (-1), .value (6), .repeat 4 19, .value (4), .value (1), .value (1)]]
  starters := [[0, 1, 88, 205, 304, 325],
    [0, 3, 8, 59, 66, 75],
    [0, 12, 26, 74, 82, 332],
    [0, 27, 155, 194, 258, 386],
    [0, 29, 55, 93, 122, 148],
    [0, 83, 221, 261, 373, 414],
    [0, 84, 195, 314, 329, 435],
    [0, 86, 164, 305, 375, 423],
    [0, 91, 185, 270, 348, 405],
    [0, 96, 208, 310, 368, 417],
    [0, 102, 227, 296, 400, 429],
    [0, 103, 177, 278, 351, 427],
    [0, 107, 226, 265, 334, 407],
    [0, 109, 228, 273, 387, 412],
    [0, 110, 172, 282, 377, 433],
    [0, 142, 239, 253, 389, 434]]

def completeOrbits40 : OrbitRecord where
  order := 441
  maps := [[.value (49), .value (27), .value (20), .value (-29), .repeat 2 3, .value (4), .value (-29), .value (20), .repeat 6 3, .value (-22), .value (-3), .repeat 5 3, .value (27), .value (-29), .value (20), .value (-3), .value (-29), .repeat 5 3, .value (20), .value (-29), .value (4), .repeat 27 5, .repeat 28 4, .repeat 27 3, .value (20), .repeat 28 3, .repeat 22 3, .value (-29), .value (46), .repeat 49 48, .value (-101), .repeat 49 48, .value (193), .repeat 147 293],
    [.value (321), .value (13), .value (-36), .value (13), .value (13), .value (13), .value (-36), .value (22), .value (13), .value (-29), .repeat 6 3, .value (13), .value (22), .repeat 13 3, .value (20), .repeat 7 6, .value (-36), .value (13), .value (20), .value (-34), .value (20), .repeat 7 4, .value (13), .value (-27), .value (13), .repeat 29 4, .repeat 7 4, .repeat 20 3, .value (-36), .value (-171), .value (13), .value (-36), .value (20), .repeat 42 7, .repeat 23 3, .repeat 42 6, .repeat 28 3, .repeat 20 4, .repeat 35 5, .repeat 52 3, .repeat 42 5, .value (13), .value (-29), .value (15), .repeat 74 3, .repeat 10 3, .value (110), .repeat 14 5, .repeat 98 6, .repeat 7 4, .repeat 69 4, .repeat 63 6, .value (-36), .value (20), .value (15), .repeat 118 5, .repeat 49 4, .repeat 44 4, .repeat 98 6, .value (13), .value (-211), .repeat 62 5, .repeat 35 7, .repeat 7 3, .repeat 91 8, .repeat 65 4, .repeat 91 6, .repeat 154 4, .repeat 84 6, .repeat 111 4, .value (-36), .value (252), .repeat 119 5, .repeat 91 5, .repeat 119 8, .repeat 98 5, .repeat 168 8, .repeat 29 3, .repeat 63 4, .repeat 168 6, .repeat 36 4, .value (67), .repeat 13 5, .repeat 14 7, .repeat 147 6, .repeat 63 7, .repeat 147 6, .repeat 63 7, .repeat 119 7, .repeat 63 3, .value (-194), .repeat 168 20, .repeat 140 6, .repeat 217 22, .value (258), .repeat 224 27, .repeat 56 21, .value (-313), .repeat 329 34, .repeat 238 5, .repeat 378 9]]
  starters := [[0, 1, 261, 293, 343, 361],
    [0, 2, 259, 289, 314, 319],
    [0, 3, 58, 92, 278, 353],
    [0, 7, 274, 286, 373, 386],
    [0, 8, 376, 391, 432, 437],
    [0, 14, 242, 362, 436, 439],
    [0, 22, 263, 323, 399, 428],
    [0, 51, 151, 223, 299, 357],
    [0, 56, 169, 231, 295, 378]]

def completeOrbits41 : OrbitRecord where
  order := 471
  maps := [[.value (5), .value (1), .repeat 1 8, .value (-14), .repeat 5 4, .value (16), .repeat 15 389, .value (11), .repeat 15 9, .repeat 1 56],
    [.value (45), .value (1), .repeat 1 3, .value (36), .repeat 5 4, .value (-24), .repeat 5 4, .value (-19), .repeat 5 4, .value (21), .repeat 5 4, .value (-9), .repeat 15 14, .repeat 30 5, .value (26), .repeat 45 44, .value (-109), .repeat 45 44, .value (161), .repeat 135 269, .value (116), .repeat 5 4, .repeat 1 61],
    [.value (135), .value (1), .repeat 1 268, .value (-400), .value (-4), .repeat 5 3, .value (6), .repeat 5 129, .value (275), .value (1), .repeat 6 3, .value (6), .repeat 5 59, .value (3)]]
  starters := [[0, 1, 2, 3, 4, 470],
    [0, 5, 60, 207, 314, 384],
    [0, 6, 232, 248, 315, 339],
    [0, 7, 153, 185, 348, 463],
    [0, 8, 151, 189, 345, 467],
    [0, 9, 269, 322, 350, 409],
    [0, 15, 40, 115, 252, 299],
    [0, 16, 122, 175, 187, 344],
    [0, 17, 177, 218, 222, 373],
    [0, 18, 65, 73, 95, 123],
    [0, 21, 176, 296, 387, 458],
    [0, 22, 76, 129, 302, 420],
    [0, 24, 178, 297, 386, 452],
    [0, 26, 113, 139, 383, 415],
    [0, 27, 61, 119, 145, 434],
    [0, 28, 64, 116, 149, 436],
    [0, 29, 108, 179, 208, 429],
    [0, 67, 156, 240, 390, 443],
    [0, 68, 158, 244, 393, 447],
    [0, 69, 264, 335, 397, 414]]

def completeOrbits42 : OrbitRecord where
  order := 486
  maps := [[.value (1), .repeat 1 95, .value (-96), .value (98), .repeat 97 387, .value (97)],
    [.value (97), .value (1), .repeat 1 386, .value (-484), .repeat 97 96, .value (389)],
    [.value (0), .value (8), .repeat 1 11, .value (-89), .repeat 12 83, .repeat 1 13, .repeat 97 376]]
  starters := [[0, 1, 122, 170, 310, 370],
    [0, 2, 119, 174, 427, 448],
    [0, 97, 194, 291, 388, 485]]

def completeOrbits43 : OrbitRecord where
  order := 501
  maps := [[.value (17), .value (1), .repeat 1 66, .value (-84), .repeat 17 16, .value (86), .repeat 85 339, .value (70), .repeat 4 3, .value (-4), .value (6), .repeat 5 64, .value (5), .repeat 76 5],
    [.value (85), .value (1), .repeat 1 338, .value (-423), .repeat 16 15, .value (-16), .value (18), .repeat 17 67, .value (357), .repeat 161 75]]
  starters := [[0, 1, 15, 223, 265, 349],
    [0, 4, 9, 100, 263, 410],
    [0, 6, 52, 88, 255, 344],
    [0, 7, 72, 94, 179, 260],
    [0, 17, 34, 51, 68, 496],
    [0, 18, 148, 157, 376, 475],
    [0, 19, 155, 208, 231, 455],
    [0, 21, 45, 320, 413, 443],
    [0, 22, 64, 120, 420, 470],
    [0, 25, 162, 289, 391, 447],
    [0, 27, 67, 167, 298, 439],
    [0, 28, 125, 339, 403, 425],
    [0, 29, 144, 296, 325, 487],
    [0, 31, 119, 156, 395, 491],
    [0, 32, 48, 236, 323, 467],
    [0, 36, 197, 306, 415, 454],
    [0, 41, 200, 335, 402, 430],
    [0, 43, 118, 159, 317, 460],
    [0, 47, 240, 277, 309, 480],
    [0, 95, 173, 268, 346, 495],
    [0, 112, 207, 319, 414, 499],
    [0, 129, 241, 285, 397, 500],
    [0, 146, 190, 336, 380, 497],
    [0, 163, 224, 302, 363, 498]]

def completeOrbits44 : OrbitRecord where
  order := 511
  maps := [[.value (1), .repeat 1 509, .value (-510)]]
  starters := [[0, 1, 82, 277, 363, 465],
    [0, 2, 29, 172, 336, 378],
    [0, 3, 104, 246, 251, 405],
    [0, 4, 157, 229, 328, 457],
    [0, 6, 43, 68, 466, 485],
    [0, 7, 205, 261, 395, 458],
    [0, 8, 23, 145, 303, 338],
    [0, 9, 20, 140, 247, 433],
    [0, 10, 49, 80, 93, 212],
    [0, 12, 33, 71, 343, 393],
    [0, 14, 111, 223, 289, 415],
    [0, 16, 105, 290, 345, 367],
    [0, 17, 156, 184, 241, 259],
    [0, 24, 65, 179, 215, 435],
    [0, 30, 64, 138, 233, 450],
    [0, 40, 92, 176, 266, 390],
    [0, 48, 165, 292, 365, 444]]

def completeOrbits45 : OrbitRecord where
  order := 591
  maps := [[.value (1), .repeat 1 101, .value (-102), .value (104), .repeat 103 411, .value (103), .repeat 77 75],
    [.value (103), .value (1), .repeat 1 410, .value (-514), .repeat 103 102, .value (414), .repeat 4 3, .value (-4), .value (6), .repeat 5 69, .value (5)],
    [.value (0), .value (56), .value (-47), .repeat 2 10, .repeat 11 44, .repeat 46 47, .repeat 103 411, .value (61), .value (1), .repeat 1 8, .value (-14), .repeat 5 4, .value (16), .repeat 15 59, .value (11)]]
  starters := [[0, 1, 86, 334, 340, 402],
    [0, 2, 51, 109, 159, 199],
    [0, 5, 48, 64, 72, 93],
    [0, 103, 206, 309, 412, 590],
    [0, 105, 281, 345, 436, 575],
    [0, 106, 266, 365, 452, 545],
    [0, 110, 245, 342, 487, 522],
    [0, 111, 230, 371, 438, 533],
    [0, 120, 244, 366, 435, 560]]

def completeOrbits46 : OrbitRecord where
  order := 621
  maps := [[.value (1), .repeat 1 107, .value (-108), .value (110), .repeat 109 435, .value (109), .repeat 77 75],
    [.value (109), .value (1), .repeat 1 434, .value (-544), .repeat 109 108, .value (438), .repeat 4 3, .value (-4), .value (6), .repeat 5 69, .value (5)],
    [.value (0), .value (45), .value (45), .value (-64), .repeat 2 3, .repeat 5 10, .repeat 12 12, .repeat 17 34, .repeat 46 46, .repeat 1 3, .repeat 109 433, .value (50), .value (1), .repeat 1 8, .value (-14), .repeat 5 4, .value (16), .repeat 15 59, .value (11)]]
  starters := [[0, 1, 41, 56, 64, 77],
    [0, 2, 5, 12, 29, 95],
    [0, 4, 75, 472, 490, 534],
    [0, 6, 57, 344, 386, 423],
    [0, 9, 31, 454, 489, 514],
    [0, 11, 252, 280, 390, 513],
    [0, 109, 218, 327, 436, 620],
    [0, 111, 238, 336, 443, 560],
    [0, 112, 254, 398, 469, 575],
    [0, 114, 304, 376, 440, 590],
    [0, 115, 260, 355, 492, 545],
    [0, 118, 243, 412, 442, 605]]

def completeOrbits47 : OrbitRecord where
  order := 646
  maps := [[.value (1), .repeat 1 35, .value (-36), .value (38), .repeat 37 517, .value (37), .repeat 556 36, .repeat 1 54],
    [.value (185), .value (26), .value (-11), .value (-11), .repeat 3 6, .repeat 7 7, .repeat 10 21, .repeat 37 332, .value (-418), .repeat 74 73, .value (-159), .repeat 185 110, .value (471), .value (1), .value (1), .value (1), .value (-4), .value (6), .repeat 5 84, .value (5)]]
  starters := [[0, 1, 22, 25, 336, 507],
    [0, 2, 28, 32, 357, 494],
    [0, 6, 29, 337, 339, 497],
    [0, 10, 112, 200, 226, 471],
    [0, 18, 93, 281, 329, 526],
    [0, 37, 74, 111, 148, 645],
    [0, 39, 107, 170, 274, 595],
    [0, 40, 175, 249, 413, 585],
    [0, 41, 97, 330, 443, 615],
    [0, 42, 95, 269, 318, 560],
    [0, 43, 78, 137, 315, 602],
    [0, 44, 261, 395, 458, 575],
    [0, 45, 113, 247, 456, 605],
    [0, 48, 171, 243, 282, 625],
    [0, 49, 218, 350, 496, 542],
    [0, 50, 116, 380, 450, 565],
    [0, 54, 398, 436, 444, 633],
    [0, 55, 88, 270, 457, 622],
    [0, 58, 199, 356, 510, 535],
    [0, 61, 140, 400, 478, 571],
    [0, 62, 157, 394, 418, 555],
    [0, 64, 151, 286, 376, 590],
    [0, 66, 142, 313, 374, 611],
    [0, 67, 291, 377, 462, 581],
    [0, 77, 287, 469, 541, 639],
    [0, 89, 216, 331, 426, 642],
    [0, 92, 228, 352, 397, 513],
    [0, 102, 244, 367, 384, 511]]

def completeOrbits48 : OrbitRecord where
  order := 691
  maps := [[.value (1), .repeat 1 689, .value (-690)]]
  starters := [[0, 1, 42, 50, 304, 480],
    [0, 2, 134, 179, 319, 362],
    [0, 3, 80, 151, 493, 561],
    [0, 4, 31, 83, 356, 453],
    [0, 5, 101, 492, 579, 682],
    [0, 6, 163, 227, 305, 363],
    [0, 7, 182, 396, 447, 465],
    [0, 10, 72, 145, 260, 467],
    [0, 11, 122, 152, 240, 259],
    [0, 12, 46, 75, 310, 419],
    [0, 13, 358, 424, 524, 577],
    [0, 15, 143, 316, 351, 598],
    [0, 16, 39, 98, 291, 475],
    [0, 17, 172, 442, 537, 592],
    [0, 20, 94, 159, 402, 562],
    [0, 21, 306, 353, 521, 547],
    [0, 22, 126, 186, 621, 659],
    [0, 24, 91, 147, 367, 404],
    [0, 25, 206, 337, 423, 529],
    [0, 28, 231, 320, 433, 494],
    [0, 33, 81, 138, 445, 535],
    [0, 36, 121, 161, 245, 522],
    [0, 44, 274, 394, 513, 589]]

def completeOrbits49 : OrbitRecord where
  order := 711
  maps := [[.value (1), .repeat 1 9, .value (-10), .value (12), .repeat 11 593, .value (11), .repeat 606 10, .repeat 1 95],
    [.value (121), .value (1), .repeat 1 482, .value (-604), .repeat 121 120, .value (486), .repeat 4 3, .value (-4), .value (6), .repeat 5 99, .value (5)],
    [.value (0), .value (11), .repeat 1 9, .value (10), .value (-110), .repeat 11 9, .value (-1), .value (11), .repeat 12 9, .value (-1), .value (11), .repeat 12 9, .repeat 11 3, .repeat 12 8, .repeat 11 4, .repeat 12 7, .repeat 11 5, .repeat 12 6, .repeat 11 6, .repeat 12 5, .repeat 11 7, .repeat 12 4, .repeat 11 8, .repeat 12 3, .repeat 11 9, .value (11), .value (-110), .value (120), .repeat 121 483, .value (125), .value (1), .repeat 1 8, .value (-14), .repeat 5 4, .value (16), .repeat 15 89, .value (11)]]
  starters := [[0, 1, 43, 60, 113, 266],
    [0, 2, 46, 69, 102, 166],
    [0, 121, 242, 363, 484, 710],
    [0, 122, 333, 401, 603, 665],
    [0, 124, 314, 422, 501, 695],
    [0, 125, 340, 416, 555, 680],
    [0, 126, 289, 407, 570, 630],
    [0, 127, 263, 461, 502, 635],
    [0, 130, 316, 394, 602, 618],
    [0, 147, 320, 427, 527, 664]]

def completeOrbits50 : OrbitRecord where
  order := 786
  maps := [[.value (1), .repeat 1 155, .value (-156), .value (158), .repeat 157 627, .value (157)],
    [.value (157), .value (1), .repeat 1 626, .value (-784), .repeat 157 156, .value (629)],
    [.value (0), .value (82), .value (-75), .repeat 2 20, .repeat 21 21, .repeat 23 46, .repeat 67 67, .value (82), .repeat 157 628]]
  starters := [[0, 1, 382, 404, 497, 603],
    [0, 2, 180, 293, 680, 735],
    [0, 157, 314, 471, 628, 785]]

def completeOrbits51 : OrbitRecord where
  order := 796
  maps := [[.value (1), .repeat 1 135, .value (-136), .value (138), .repeat 137 547, .value (137), .repeat 112 110],
    [.value (137), .value (1), .repeat 1 546, .value (-684), .repeat 137 136, .value (550), .repeat 4 3, .value (-4), .value (6), .repeat 5 104, .value (5)]]
  starters := [[0, 1, 113, 298, 361, 371],
    [0, 2, 41, 579, 616, 682],
    [0, 3, 35, 107, 195, 214],
    [0, 4, 56, 275, 291, 381],
    [0, 5, 13, 59, 82, 97],
    [0, 6, 17, 168, 210, 254],
    [0, 7, 28, 50, 108, 117],
    [0, 12, 26, 88, 391, 409],
    [0, 137, 274, 411, 548, 795],
    [0, 138, 294, 512, 564, 775],
    [0, 139, 285, 444, 649, 735],
    [0, 141, 403, 489, 590, 741],
    [0, 143, 346, 475, 661, 685],
    [0, 144, 292, 511, 549, 783],
    [0, 145, 384, 468, 637, 722],
    [0, 149, 301, 465, 569, 706],
    [0, 150, 351, 440, 559, 755],
    [0, 153, 331, 488, 587, 745],
    [0, 154, 328, 495, 557, 765],
    [0, 155, 343, 418, 651, 725],
    [0, 158, 352, 446, 570, 772],
    [0, 163, 295, 502, 632, 699],
    [0, 165, 279, 509, 572, 761],
    [0, 166, 284, 504, 613, 753],
    [0, 170, 342, 539, 642, 785],
    [0, 176, 359, 482, 609, 690],
    [0, 177, 406, 526, 631, 716],
    [0, 182, 398, 459, 550, 704],
    [0, 184, 386, 520, 607, 794],
    [0, 187, 309, 442, 573, 731],
    [0, 196, 281, 515, 595, 710]]

def completeOrbits52 : OrbitRecord where
  order := 801
  maps := [[.value (29), .value (1), .repeat 1 114, .value (-144), .repeat 29 28, .value (146), .repeat 145 579, .value (118), .repeat 4 3, .value (-4), .value (6), .repeat 5 64, .value (5), .repeat 76 5],
    [.value (145), .value (1), .repeat 1 578, .value (-723), .repeat 28 27, .value (-28), .value (30), .repeat 29 115, .value (609), .repeat 221 75]]
  starters := [[0, 1, 8, 152, 170, 316],
    [0, 2, 167, 450, 581, 600],
    [0, 3, 12, 159, 447, 463],
    [0, 4, 161, 298, 456, 461],
    [0, 6, 127, 344, 383, 500],
    [0, 14, 103, 265, 627, 652],
    [0, 29, 58, 87, 116, 796],
    [0, 30, 243, 501, 564, 745],
    [0, 31, 130, 179, 400, 663],
    [0, 32, 240, 356, 439, 551],
    [0, 34, 139, 233, 376, 476],
    [0, 36, 219, 535, 573, 744],
    [0, 37, 359, 682, 702, 756],
    [0, 39, 91, 225, 286, 739],
    [0, 40, 86, 524, 697, 768],
    [0, 41, 100, 355, 722, 734],
    [0, 42, 102, 283, 493, 617],
    [0, 43, 126, 370, 392, 772],
    [0, 45, 272, 329, 540, 639],
    [0, 50, 94, 512, 705, 787],
    [0, 52, 78, 424, 683, 753],
    [0, 56, 232, 648, 718, 782],
    [0, 57, 110, 206, 409, 482],
    [0, 65, 171, 239, 330, 709],
    [0, 66, 237, 341, 419, 791],
    [0, 76, 154, 402, 579, 635],
    [0, 79, 234, 616, 706, 777],
    [0, 168, 307, 446, 585, 795],
    [0, 190, 406, 550, 654, 763],
    [0, 197, 365, 533, 701, 800],
    [0, 198, 396, 518, 699, 725],
    [0, 226, 423, 475, 672, 798],
    [0, 255, 336, 562, 643, 799],
    [0, 284, 394, 504, 614, 797]]

def completeOrbits53 : OrbitRecord where
  order := 886
  maps := [[.value (1), .repeat 1 29, .value (-30), .value (32), .repeat 31 743, .value (31), .repeat 776 30, .repeat 1 80],
    [.value (31), .value (1), .repeat 1 122, .value (-154), .repeat 31 30, .value (156), .repeat 155 619, .value (126), .repeat 4 3, .value (-4), .value (6), .repeat 5 99, .value (5), .repeat 111 5],
    [.value (155), .value (1), .repeat 1 618, .value (-774), .repeat 155 154, .value (621), .repeat 111 110],
    [.value (0), .value (5), .repeat 1 5, .value (-26), .repeat 6 23, .repeat 1 7, .repeat 31 737, .value (10), .value (1), .repeat 1 8, .value (-14), .repeat 5 4, .value (16), .repeat 15 89, .value (11), .repeat 11 5]]
  starters := [[0, 1, 6, 33, 42, 56],
    [0, 2, 21, 534, 549, 552],
    [0, 4, 174, 319, 480, 644],
    [0, 31, 62, 93, 124, 880],
    [0, 34, 404, 457, 691, 835],
    [0, 35, 222, 542, 617, 689],
    [0, 37, 243, 453, 479, 635],
    [0, 39, 120, 235, 440, 819],
    [0, 43, 294, 391, 727, 823],
    [0, 47, 95, 246, 309, 854],
    [0, 68, 200, 300, 559, 776],
    [0, 70, 249, 370, 447, 871],
    [0, 155, 310, 465, 620, 885],
    [0, 186, 372, 558, 744, 881],
    [0, 217, 434, 496, 713, 883],
    [0, 221, 355, 602, 730, 792],
    [0, 248, 341, 589, 682, 882],
    [0, 279, 403, 527, 651, 884]]

def completeOrbits : List ((Nat × Nat) × OrbitRecord) := [
  ((1, 0), completeOrbits0),
  ((6, 0), completeOrbits1),
  ((31, 0), completeOrbits2),
  ((66, 0), design66),
  ((76, 0), completeOrbits4),
  ((91, 0), design91),
  ((96, 0), completeOrbits6),
  ((106, 0), completeOrbits7),
  ((111, 0), completeOrbits8),
  ((121, 0), completeOrbits9),
  ((126, 0), completeOrbits10),
  ((136, 0), completeOrbits11),
  ((141, 0), completeOrbits12),
  ((151, 0), completeOrbits13),
  ((166, 0), completeOrbits14),
  ((171, 0), completeOrbits15),
  ((181, 0), completeOrbits16),
  ((196, 0), completeOrbits17),
  ((201, 0), completeOrbits18),
  ((216, 0), completeOrbits19),
  ((226, 0), completeOrbits20),
  ((241, 0), completeOrbits21),
  ((261, 0), completeOrbits22),
  ((271, 0), completeOrbits23),
  ((286, 0), completeOrbits24),
  ((291, 0), completeOrbits25),
  ((301, 0), completeOrbits26),
  ((306, 0), completeOrbits27),
  ((316, 0), completeOrbits28),
  ((321, 6), completeOrbits29),
  ((336, 31), completeOrbits30),
  ((346, 31), completeOrbits31),
  ((351, 0), completeOrbits32),
  ((361, 0), completeOrbits33),
  ((366, 0), completeOrbits34),
  ((376, 0), completeOrbits35),
  ((406, 0), completeOrbits36),
  ((411, 6), completeOrbits37),
  ((421, 0), completeOrbits38),
  ((436, 31), completeOrbits39),
  ((441, 0), completeOrbits40),
  ((471, 66), completeOrbits41),
  ((486, 0), completeOrbits42),
  ((501, 76), completeOrbits43),
  ((511, 0), completeOrbits44),
  ((591, 76), completeOrbits45),
  ((621, 76), completeOrbits46),
  ((646, 91), completeOrbits47),
  ((691, 0), completeOrbits48),
  ((711, 106), completeOrbits49),
  ((786, 0), completeOrbits50),
  ((796, 111), completeOrbits51),
  ((801, 76), completeOrbits52),
  ((886, 111), completeOrbits53)
]

def incompleteOrbits2 : OrbitRecord where
  order := 126
  maps := [[.value (1), .repeat 1 5, .value (-6), .value (8), .repeat 7 118],
    [.value (7), .value (1), .repeat 1 26, .value (-34), .repeat 7 6, .value (36), .repeat 35 69, .value (29), .repeat 28 20],
    [.value (35), .value (4), .value (-3), .repeat 2 5, .repeat 7 62, .value (-101), .repeat 35 34, .value (81), .repeat 14 13, .value (-17), .repeat 7 6]]
  starters := [[0, 1, 16, 62, 84, 115],
    [0, 2, 31, 43, 69, 111],
    [0, 3, 53, 66, 102, 110],
    [0, 7, 14, 21, 28, 105],
    [0, 8, 30, 89, 93, 112],
    [0, 10, 39, 44, 76, 82],
    [0, 17, 40, 52, 74, 87]]

def incompleteOrbits3 : OrbitRecord where
  order := 131
  maps := [[.value (7), .value (1), .repeat 1 26, .value (-34), .repeat 7 6, .value (36), .repeat 35 69, .value (30), .repeat 4 3, .value (-4), .value (5), .repeat 33 20],
    [.value (35), .value (1), .repeat 1 68, .value (-103), .repeat 6 5, .value (-6), .value (8), .repeat 7 27, .value (77), .repeat 6 4, .repeat 12 6, .repeat 1 8, .value (-19), .repeat 26 6]]
  starters := [[0, 1, 3, 36, 101, 126],
    [0, 7, 14, 21, 28, 110],
    [0, 8, 31, 86, 95, 105],
    [0, 10, 25, 54, 67, 123],
    [0, 12, 66, 77, 103, 127],
    [0, 13, 56, 83, 94, 121]]

def incompleteOrbits4 : OrbitRecord where
  order := 166
  maps := [[.value (1), .repeat 1 27, .value (-28), .value (30), .repeat 29 115, .value (29), .repeat 22 20],
    [.value (29), .value (1), .repeat 1 114, .value (-144), .repeat 29 28, .value (118), .repeat 4 3, .value (-4), .value (6), .repeat 5 14, .value (5)]]
  starters := [[0, 1, 3, 19, 25, 41],
    [0, 8, 20, 44, 101, 115],
    [0, 29, 58, 87, 116, 165],
    [0, 30, 77, 104, 143, 158],
    [0, 32, 69, 94, 122, 164],
    [0, 33, 75, 96, 131, 150],
    [0, 34, 60, 106, 125, 149]]

def incompleteOrbits5 : OrbitRecord where
  order := 171
  maps := [[.value (1), .repeat 1 29, .value (-30), .value (32), .repeat 31 123, .value (31), .repeat 17 15],
    [.value (31), .value (1), .repeat 1 122, .value (-154), .repeat 31 30, .value (126), .repeat 4 3, .value (-4), .value (6), .repeat 5 9, .value (5)]]
  starters := [[0, 1, 5, 14, 20, 56],
    [0, 2, 92, 110, 113, 120],
    [0, 8, 61, 88, 117, 151],
    [0, 31, 62, 93, 124, 170],
    [0, 32, 72, 116, 132, 155],
    [0, 33, 71, 112, 138, 160],
    [0, 37, 82, 101, 140, 165]]

def incompleteOrbits6 : OrbitRecord where
  order := 196
  maps := [[.value (7), .value (1), .repeat 1 26, .value (-34), .repeat 7 6, .value (36), .repeat 35 139, .value (30), .repeat 4 3, .value (-4), .value (6), .repeat 5 14, .value (5)],
    [.value (35), .value (1), .repeat 1 138, .value (-173), .repeat 6 5, .value (-6), .value (8), .repeat 7 27, .value (147), .repeat 56 20]]
  starters := [[0, 1, 85, 108, 113, 174],
    [0, 2, 13, 70, 142, 146],
    [0, 7, 14, 21, 28, 195],
    [0, 8, 33, 128, 160, 194],
    [0, 10, 22, 60, 93, 148],
    [0, 15, 59, 81, 136, 185],
    [0, 16, 46, 91, 138, 179],
    [0, 18, 69, 83, 129, 184]]

def incompleteOrbits7 : OrbitRecord where
  order := 206
  maps := [[.value (1), .repeat 1 80, .value (-81), .value (83), .repeat 82 81, .value (82), .value (2), .repeat 42 39, .value (-40)],
    [.value (82), .value (1), .repeat 1 80, .value (-107), .repeat 26 25, .value (-81), .repeat 82 55, .value (109), .value (29), .repeat 14 12, .value (-40), .repeat 42 27]]
  starters := [[0, 1, 50, 75, 109, 185],
    [0, 2, 22, 39, 85, 177],
    [0, 3, 15, 115, 153, 181],
    [0, 4, 58, 93, 162, 167],
    [0, 5, 23, 71, 126, 203],
    [0, 6, 52, 94, 129, 194],
    [0, 9, 51, 72, 142, 199],
    [0, 14, 106, 132, 161, 170],
    [0, 41, 95, 136, 164, 165]]

def incompleteOrbits8 : OrbitRecord where
  order := 226
  maps := [[.value (1), .repeat 1 39, .value (-40), .value (42), .repeat 41 163, .value (41), .repeat 22 20],
    [.value (41), .value (1), .repeat 1 162, .value (-204), .repeat 41 40, .value (166), .repeat 4 3, .value (-4), .value (6), .repeat 5 14, .value (5)]]
  starters := [[0, 1, 14, 22, 26, 45],
    [0, 2, 5, 11, 85, 103],
    [0, 7, 47, 78, 93, 187],
    [0, 17, 55, 112, 155, 188],
    [0, 41, 82, 123, 164, 225],
    [0, 42, 109, 141, 170, 221],
    [0, 48, 97, 162, 184, 205],
    [0, 50, 104, 157, 185, 210],
    [0, 51, 119, 130, 166, 215]]

def incompleteOrbits9 : OrbitRecord where
  order := 246
  maps := [[.value (1), .repeat 1 41, .value (-42), .value (44), .repeat 43 171, .value (43), .repeat 32 30],
    [.value (43), .value (1), .repeat 1 170, .value (-214), .repeat 43 42, .value (174), .repeat 4 3, .value (-4), .value (6), .repeat 5 24, .value (5)]]
  starters := [[0, 1, 8, 10, 21, 39],
    [0, 3, 63, 69, 181, 209],
    [0, 16, 107, 124, 149, 168],
    [0, 43, 86, 129, 172, 245],
    [0, 45, 102, 164, 175, 215],
    [0, 46, 87, 159, 183, 231],
    [0, 47, 117, 170, 185, 220],
    [0, 48, 122, 158, 180, 225],
    [0, 50, 114, 165, 203, 243],
    [0, 56, 95, 154, 187, 236]]

def incompleteOrbits10 : OrbitRecord where
  order := 261
  maps := [[.value (1), .repeat 1 47, .value (-48), .value (50), .repeat 49 195, .value (49), .repeat 17 15],
    [.value (132), .value (-19), .value (30), .value (-19), .repeat 3 3, .repeat 5 5, .repeat 8 8, .repeat 13 18, .repeat 18 11, .value (79), .repeat 49 97, .value (-166), .repeat 98 97, .value (197), .value (1), .repeat 1 8, .value (-13), .repeat 4 3, .value (-4), .value (15)]]
  starters := [[0, 1, 46, 173, 186, 206],
    [0, 6, 119, 207, 216, 244],
    [0, 49, 98, 147, 196, 260],
    [0, 52, 116, 188, 219, 246]]

def incompleteOrbits11 : OrbitRecord where
  order := 266
  maps := [[.value (5), .value (1), .repeat 1 18, .value (-24), .repeat 5 4, .value (26), .repeat 25 199, .value (22), .repeat 4 3, .value (-4), .value (6), .repeat 5 34, .value (5)],
    [.value (25), .value (1), .repeat 1 48, .value (-71), .value (1), .value (-4), .value (1), .value (1), .value (6), .repeat 5 19, .value (78), .repeat 75 149, .value (53), .repeat 66 40],
    [.value (75), .value (1), .repeat 1 148, .value (-224), .repeat 75 74, .value (151), .repeat 41 40]]
  starters := [[0, 1, 2, 3, 4, 265],
    [0, 5, 26, 50, 102, 201],
    [0, 6, 49, 138, 216, 259],
    [0, 7, 42, 187, 220, 225],
    [0, 8, 112, 199, 217, 261],
    [0, 9, 41, 120, 185, 250],
    [0, 10, 77, 126, 152, 177],
    [0, 11, 82, 145, 219, 238],
    [0, 12, 74, 165, 206, 234],
    [0, 13, 55, 71, 144, 241],
    [0, 34, 95, 115, 161, 246]]

def incompleteOrbits12 : OrbitRecord where
  order := 276
  maps := [[.value (1), .repeat 1 47, .value (-48), .value (50), .repeat 49 195, .value (49), .repeat 32 30],
    [.value (49), .value (1), .repeat 1 194, .value (-244), .repeat 49 48, .value (198), .repeat 4 3, .value (-4), .value (6), .repeat 5 24, .value (5)]]
  starters := [[0, 1, 8, 10, 23, 94],
    [0, 3, 24, 58, 90, 190],
    [0, 4, 16, 35, 109, 138],
    [0, 5, 43, 75, 144, 240],
    [0, 49, 98, 147, 196, 275],
    [0, 50, 111, 176, 227, 245],
    [0, 52, 112, 188, 231, 250],
    [0, 53, 125, 161, 217, 255],
    [0, 57, 131, 170, 203, 260],
    [0, 62, 140, 159, 205, 265],
    [0, 64, 137, 184, 215, 270]]

def incompleteOrbits : List ((Nat × Nat) × OrbitRecord) := [
  ((81, 16), incomplete81),
  ((106, 21), incomplete106),
  ((126, 21), incompleteOrbits2),
  ((131, 26), incompleteOrbits3),
  ((166, 21), incompleteOrbits4),
  ((171, 16), incompleteOrbits5),
  ((196, 21), incompleteOrbits6),
  ((206, 41), incompleteOrbits7),
  ((226, 21), incompleteOrbits8),
  ((246, 31), incompleteOrbits9),
  ((261, 16), incompleteOrbits10),
  ((266, 41), incompleteOrbits11),
  ((276, 31), incompleteOrbits12)
]

def groupOrbits0 : OrbitRecord where
  order := 84
  maps := [[.value (1), .repeat 1 19, .value (-20), .value (22), .repeat 21 62],
    [.value (20), .value (-5), .repeat 1 3, .value (16), .repeat 4 15, .value (30), .repeat 11 10, .repeat 24 10, .value (5), .repeat 34 12, .repeat 9 8, .repeat 42 3, .repeat 62 17, .value (-5)],
    [.value (21), .value (8), .value (8), .value (-13), .repeat 3 4, .repeat 5 5, .repeat 8 8, .value (-34), .repeat 21 20, .value (50), .repeat 42 41]]
  starters := [[0, 1, 5, 22, 33, 35],
    [0, 2, 31, 61, 65, 69],
    [0, 7, 53, 64, 75, 83],
    [42, 49, 56, 63, 70, 77]]

def groupOrbits1 : OrbitRecord where
  order := 90
  maps := [[.value (0), .value (1), .repeat 1 4, .value (2), .repeat 6 5, .repeat 1 8, .value (-14), .value (15), .repeat 9 7, .repeat 23 15, .value (16), .repeat 15 44, .value (15)],
    [.value (0), .value (1), .value (1), .value (1), .value (2), .value (-1), .value (2), .value (4), .value (4), .value (4), .value (-11), .repeat 4 10, .value (5), .value (-1), .value (3), .repeat 2 5, .value (17), .repeat 23 14, .value (-26), .repeat 15 14, .value (34), .repeat 30 29, .value (19)],
    [.value (1), .value (-1), .value (3), .value (-1), .value (2), .value (1), .value (1), .value (11), .value (-4), .value (-4), .repeat 3 3, .repeat 4 8, .value (13), .value (1), .value (-3), .value (1), .value (5), .repeat 4 3, .value (18), .repeat 23 14, .value (-19), .repeat 15 14, .value (41), .repeat 30 29, .value (26)]]
  starters := [[0, 6, 30, 48, 67, 76],
    [2, 6, 31, 52, 65, 83],
    [4, 6, 37, 57, 64, 84],
    [6, 21, 38, 54, 70, 78],
    [6, 25, 41, 58, 61, 77],
    [6, 29, 44, 59, 74, 89]]

def groupOrbits2 : OrbitRecord where
  order := 108
  maps := [[.value (1), .value (1), .value (-2), .value (4), .repeat 3 50, .value (3), .value (1), .repeat 1 16, .value (2), .repeat 54 35],
    [.value (3), .value (1), .repeat 1 4, .value (-8), .value (1), .value (1), .value (10), .repeat 9 44, .value (8), .value (1), .value (-2), .value (4), .repeat 3 14, .value (6), .repeat 36 17, .value (7), .repeat 9 5, .repeat 1 12],
    [.value (2), .value (-2), .value (1), .value (4), .repeat 3 14, .value (10), .value (-2), .value (1), .value (-5), .repeat 9 5, .value (13), .repeat 9 8, .value (8), .value (1), .repeat 1 4, .value (-8), .value (1), .value (1), .value (10), .repeat 9 26, .value (11), .value (1), .value (-2), .value (4), .value (1), .value (-2), .value (-5), .value (1), .value (-2), .value (13), .repeat 9 8, .value (12), .repeat 36 17]]
  starters := [[0, 18, 36, 54, 72, 90],
    [0, 19, 47, 67, 75, 102],
    [0, 20, 39, 61, 87, 104],
    [0, 27, 37, 63, 88, 95],
    [0, 28, 51, 68, 76, 99],
    [0, 29, 53, 62, 84, 93],
    [9, 18, 44, 68, 74, 91],
    [9, 19, 50, 66, 86, 94],
    [9, 20, 47, 59, 85, 106],
    [9, 27, 45, 55, 72, 93],
    [9, 28, 39, 70, 84, 100],
    [9, 29, 37, 57, 80, 103]]

def groupOrbits3 : OrbitRecord where
  order := 120
  maps := [[.value (0), .value (1), .value (1), .value (2), .value (1), .value (-2), .value (4), .value (11), .value (-8), .repeat 2 4, .repeat 5 10, .value (11), .value (-8), .value (14), .repeat 17 16, .value (-8), .value (11), .value (13), .repeat 12 11, .repeat 5 7, .value (24), .repeat 16 11, .repeat 7 8, .repeat 19 18, .value (-46), .repeat 19 18],
    [.value (3), .value (1), .value (1), .value (-4), .value (1), .value (-2), .value (63), .value (11), .value (-8), .repeat 2 4, .repeat 5 5, .repeat 7 7, .value (14), .repeat 17 16, .value (-8), .value (11), .value (8), .repeat 38 18, .value (-84), .repeat 19 18, .value (16), .repeat 15 14, .repeat 7 4, .value (-51), .repeat 38 18]]
  starters := [[0, 1, 2, 3, 4, 5],
    [0, 25, 59, 63, 97, 110],
    [6, 25, 44, 77, 88, 103],
    [6, 26, 52, 73, 99, 105],
    [6, 27, 60, 80, 92, 114]]

def groupOrbits4 : OrbitRecord where
  order := 135
  maps := [[.value (1), .repeat 1 133, .value (-134)]]
  starters := [[0, 1, 22, 42, 128, 131],
    [0, 2, 12, 62, 68, 100],
    [0, 11, 34, 51, 64, 121],
    [0, 15, 39, 58, 91, 119]]

def groupOrbits6 : OrbitRecord where
  order := 210
  maps := [[.value (1), .repeat 1 208, .value (-209)]]
  starters := [[0, 1, 83, 177, 186, 208],
    [0, 4, 51, 59, 117, 146],
    [0, 5, 76, 162, 172, 178],
    [0, 11, 50, 90, 110, 191],
    [0, 12, 57, 74, 149, 195],
    [0, 13, 65, 143, 169, 187]]

def groupOrbits7 : OrbitRecord where
  order := 225
  maps := [[.value (0), .value (1), .repeat 1 23, .value (2), .repeat 4 3, .value (-4), .value (6), .repeat 5 194],
    [.value (25), .value (5), .repeat 1 3, .value (-19), .repeat 5 19, .value (1), .repeat 25 24, .value (-74), .value (1), .repeat 1 23, .value (76), .repeat 30 4, .value (-16), .repeat 5 4, .value (-21), .repeat 5 14, .value (4), .value (4), .value (-1), .value (-1), .value (-1), .repeat 5 20, .value (-71), .repeat 100 24, .repeat 75 5, .repeat 150 25, .value (-18), .repeat 5 9, .value (-23), .repeat 10 9, .value (-73), .value (3), .value (-2), .repeat 2 3, .repeat 5 19]]
  starters := [[0, 25, 50, 169, 198, 218],
    [0, 30, 120, 146, 153, 206],
    [0, 35, 78, 138, 192, 201],
    [0, 40, 63, 80, 111, 127],
    [0, 45, 86, 108, 159, 179],
    [75, 100, 125, 150, 175, 200]]

def groupOrbits8 : OrbitRecord where
  order := 250
  maps := [[.value (1), .repeat 1 3, .value (-4), .value (6), .repeat 5 244],
    [.value (21), .value (91), .value (-31), .value (-23), .value (-20), .value (51), .value (-28), .value (-20), .value (-37), .value (111), .value (-66), .value (-42), .value (116), .value (-31), .value (-23), .value (32), .value (-6), .value (-23), .value (-45), .value (-17), .value (40), .value (-20), .value (-12), .value (91), .value (-31), .value (-56), .value (80), .value (-17), .value (-34), .value (-6), .value (48), .value (-34), .value (-31), .value (-28), .value (105), .value (-74), .value (-23), .value (105), .value (-17), .value (-34), .value (54), .value (-37), .value (-14), .value (-26), .value (-28), .value (62), .value (-31), .value (-23), .value (105), .value (-42), .value (-59), .value (94), .value (-23), .value (-20), .value (-42), .value (65), .value (-45), .value (-17), .value (-34), .value (119), .value (-77), .value (-34), .value (94), .value (-28), .value (-20), .value (51), .value (-23), .value (-20), .repeat 30 5, .value (99), .value (-28), .value (-62), .value (83), .value (-9), .repeat 65 6, .value (108), .value (-85), .value (-20), .value (113), .value (-34), .value (-31), .value (68), .value (-34), .repeat 90 6, .value (88), .value (-14), .value (-70), .value (102), .repeat 46 3, .value (54), .value (-12), .value (-34), .value (-31), .value (97), .value (-63), .value (-31), .value (102), .value (-20), .repeat 95 3, .repeat 76 3, .value (43), .value (-9), .repeat 11 3, .value (81), .value (-12), .repeat 66 3, .value (-63), .repeat 80 3, .repeat 20 5, .value (99), .value (-82), .value (-9), .repeat 11 3, .value (46), .repeat 129 3, .value (-34), .value (55), .value (-23), .value (-20), .value (108), .value (-34), .value (-71), .value (88), .repeat 115 6, .value (-20), .value (83), .value (-60), .value (-45), .value (108), .repeat 140 6, .value (-20), .value (52), .repeat 55 4, .value (-79), .repeat 80 19, .value (44), .value (-20), .value (-17), .value (91), .value (-31), .value (-77), .value (111), .value (-26), .repeat 145 5, .value (-42), .value (116), .value (-96), .value (-17), .value (91), .value (-6), .value (-23), .value (37), .repeat 49 3, .value (-12), .value (41), .repeat 194 3, .value (-12), .value (-85), .repeat 194 3, .value (-31), .value (48), .repeat 79 3, .repeat 205 4, .value (-42), .value (-9), .value (29), .repeat 219 3, .value (-23)]]
  starters := [[0, 1, 18, 34, 154, 235],
    [0, 5, 28, 163, 165, 223],
    [0, 7, 134, 186, 213, 233]]

def groupOrbits9 : OrbitRecord where
  order := 490
  maps := [[.value (49), .value (1), .repeat 1 194, .value (-235), .repeat 5 4, .value (-6), .value (1), .value (8), .repeat 7 34, .value (-41), .repeat 7 6, .value (293), .repeat 245 244],
    [.value (245), .value (1), .repeat 1 243, .value (-488), .repeat 6 5, .value (-6), .value (8), .repeat 7 237]]
  starters := [[0, 1, 52, 133, 234, 415],
    [0, 2, 63, 129, 225, 401],
    [0, 3, 47, 147, 270, 385],
    [0, 8, 56, 80, 301, 317],
    [0, 10, 155, 335, 363, 489],
    [0, 11, 37, 108, 246, 432],
    [0, 13, 87, 253, 352, 377],
    [0, 15, 91, 176, 223, 358],
    [0, 17, 132, 306, 361, 388],
    [0, 18, 123, 294, 403, 447],
    [0, 20, 95, 219, 287, 413],
    [0, 26, 94, 149, 232, 349],
    [0, 27, 97, 238, 259, 384],
    [0, 49, 102, 272, 330, 391]]

def groupOrbits10 : OrbitRecord where
  order := 525
  maps := [[.value (1), .repeat 1 523, .value (-524)]]
  starters := [[0, 1, 60, 226, 335, 500],
    [0, 2, 73, 286, 351, 494],
    [0, 3, 78, 230, 355, 375],
    [0, 4, 127, 395, 436, 510],
    [0, 5, 137, 296, 477, 493],
    [0, 6, 67, 327, 430, 513],
    [0, 8, 30, 179, 222, 437],
    [0, 9, 66, 244, 271, 428],
    [0, 10, 68, 209, 445, 491],
    [0, 11, 122, 324, 405, 512],
    [0, 17, 86, 237, 365, 404],
    [0, 23, 52, 99, 139, 431],
    [0, 36, 172, 223, 285, 367],
    [0, 38, 92, 221, 345, 453],
    [0, 45, 200, 264, 314, 470]]

def groupOrbits : List ((List Nat) × OrbitRecord) := [
  (([14, 14, 14, 14, 14, 14]), groupOrbits0),
  (([15, 15, 15, 15, 15, 15]), groupOrbits1),
  (([18, 18, 18, 18, 18, 18]), groupOrbits2),
  (([20, 20, 20, 20, 20, 20]), groupOrbits3),
  (([15, 15, 15, 15, 15, 15, 15, 15, 15]), groupOrbits4),
  (([30, 30, 30, 30, 30, 30, 30]), groupOrbits6),
  (([25, 25, 25, 25, 25, 25, 25, 25, 25]), groupOrbits7),
  (([25, 25, 25, 25, 25, 25, 25, 25, 25, 25]), groupOrbits8),
  (([70, 70, 70, 70, 70, 70, 70]), groupOrbits9),
  (([75, 75, 75, 75, 75, 75, 75]), groupOrbits10)
]

def arrayOrbits0 : OrbitRecord where
  order := 102
  maps := [[.value (1), .repeat 1 13, .value (-14), .value (16), .repeat 15 74, .value (15), .repeat 13 11],
    [.value (0), .value (14), .value (-1), .repeat 1 12, .value (14), .repeat 15 74, .value (15), .value (-1), .value (3), .repeat 2 9]]
  starters := [[0, 15, 30, 45, 60, 75],
    [0, 16, 36, 58, 69, 85],
    [0, 17, 31, 56, 78, 98],
    [0, 18, 37, 46, 74, 100],
    [0, 19, 32, 73, 84, 96],
    [0, 20, 42, 54, 70, 82],
    [0, 21, 50, 68, 89, 94],
    [0, 22, 40, 57, 64, 86],
    [0, 34, 53, 63, 88, 92],
    [15, 36, 52, 61, 78, 90]]

def arrayOrbits1 : OrbitRecord where
  order := 108
  maps := [[.value (1), .value (1), .value (-2), .value (4), .repeat 3 14, .value (8), .value (1), .repeat 1 8, .value (-14), .repeat 5 4, .value (16), .repeat 15 74],
    [.value (2), .value (-2), .value (1), .value (4), .repeat 3 14, .value (17), .value (1), .repeat 1 28, .value (-43), .repeat 4 3, .value (-4), .value (6), .repeat 5 9, .value (50), .repeat 45 44]]
  starters := [[0, 23, 55, 72, 80, 106],
    [3, 23, 36, 66, 94, 98],
    [6, 23, 32, 82, 85, 92],
    [9, 18, 30, 44, 72, 73],
    [12, 18, 32, 45, 71, 100],
    [15, 18, 28, 52, 74, 94],
    [18, 25, 34, 70, 84, 102]]

def arrayOrbits2 : OrbitRecord where
  order := 462
  maps := [[.value (1), .repeat 1 11, .value (-12), .value (14), .repeat 13 376, .value (13), .repeat 391 12, .repeat 1 59],
    [.value (0), .value (3), .repeat 1 3, .value (-10), .repeat 4 7, .repeat 1 5, .repeat 13 372, .value (4), .value (1), .value (-2), .repeat 3 69],
    [.value (0), .value (1), .repeat 1 76, .value (27), .repeat 26 25, .value (-38), .repeat 13 12, .value (-25), .repeat 13 12, .value (66), .repeat 52 259, .value (46), .repeat 6 5, .value (-8), .value (1), .value (1), .value (-5), .value (1), .value (1), .value (16), .repeat 12 59]]
  starters := [[0, 13, 26, 39, 52, 65],
    [0, 14, 28, 42, 56, 70],
    [0, 15, 30, 45, 60, 75],
    [0, 17, 34, 51, 55, 72],
    [0, 20, 27, 47, 54, 74],
    [0, 130, 208, 273, 299, 338],
    [0, 131, 211, 280, 301, 450],
    [0, 132, 214, 274, 363, 438],
    [0, 134, 220, 335, 362, 426],
    [0, 137, 262, 336, 354, 416],
    [0, 189, 270, 328, 353, 403],
    [13, 78, 195, 273, 312, 351],
    [13, 79, 206, 330, 372, 430],
    [13, 80, 254, 335, 367, 418],
    [13, 82, 200, 275, 321, 455],
    [13, 85, 207, 283, 368, 442],
    [13, 183, 263, 332, 353, 390],
    [26, 78, 169, 260, 299, 364],
    [26, 79, 174, 323, 363, 432],
    [26, 80, 248, 328, 371, 405],
    [26, 82, 176, 272, 309, 457],
    [26, 85, 178, 268, 357, 444],
    [26, 134, 252, 327, 373, 395],
    [39, 78, 143, 208, 325, 377],
    [39, 79, 233, 314, 357, 408],
    [39, 80, 154, 211, 332, 461],
    [39, 82, 152, 214, 385, 449],
    [39, 85, 171, 313, 354, 420],
    [39, 134, 228, 324, 361, 397],
    [52, 78, 156, 221, 247, 338],
    [52, 79, 154, 213, 386, 437],
    [52, 80, 152, 264, 382, 425],
    [52, 82, 207, 268, 387, 413],
    [52, 85, 166, 224, 249, 451],
    [52, 132, 206, 263, 384, 401],
    [65, 78, 130, 182, 234, 286],
    [65, 79, 159, 228, 249, 438],
    [65, 80, 162, 222, 311, 426],
    [65, 82, 168, 283, 310, 414],
    [65, 85, 210, 284, 302, 404],
    [65, 137, 218, 276, 301, 391],
    [78, 131, 184, 237, 290, 343],
    [78, 132, 186, 240, 294, 348],
    [78, 134, 190, 246, 289, 345],
    [78, 137, 183, 242, 288, 347]]

def arrayOrbits3 : OrbitRecord where
  order := 612
  maps := [[.value (1), .repeat 1 15, .value (-16), .value (18), .repeat 17 492, .value (17), .repeat 511 16, .repeat 1 85],
    [.value (17), .value (1), .repeat 1 66, .value (-84), .repeat 17 16, .value (86), .repeat 85 424, .value (69), .repeat 85 67, .repeat 1 34]]
  starters := [[0, 85, 170, 255, 340, 425],
    [0, 86, 172, 258, 344, 430],
    [0, 87, 174, 261, 348, 435],
    [0, 88, 176, 264, 352, 440],
    [0, 89, 178, 267, 356, 428],
    [0, 90, 180, 270, 343, 433],
    [0, 91, 182, 256, 347, 438],
    [0, 92, 184, 259, 351, 426],
    [0, 93, 186, 262, 355, 431],
    [0, 94, 171, 265, 342, 436],
    [0, 95, 173, 268, 346, 441],
    [0, 96, 175, 271, 350, 429],
    [0, 97, 177, 257, 354, 434],
    [0, 98, 179, 260, 341, 439],
    [0, 99, 181, 263, 345, 427],
    [0, 100, 183, 266, 349, 432],
    [0, 101, 185, 269, 353, 437],
    [0, 102, 243, 308, 379, 599],
    [0, 103, 254, 381, 479, 573],
    [0, 104, 327, 399, 464, 547],
    [0, 105, 325, 404, 467, 549],
    [0, 106, 311, 388, 504, 550],
    [0, 107, 332, 382, 476, 560],
    [0, 108, 301, 394, 503, 551],
    [0, 109, 251, 317, 468, 580],
    [0, 110, 226, 334, 474, 585],
    [0, 111, 292, 405, 500, 559],
    [0, 112, 310, 380, 495, 554],
    [0, 113, 235, 329, 463, 593],
    [0, 114, 241, 293, 488, 586],
    [0, 115, 248, 307, 466, 592],
    [0, 116, 231, 305, 498, 591],
    [0, 117, 227, 291, 496, 589],
    [0, 118, 244, 389, 478, 565],
    [0, 119, 238, 272, 391, 595],
    [0, 120, 188, 306, 493, 578],
    [0, 121, 246, 313, 443, 579],
    [0, 122, 233, 414, 452, 576],
    [0, 123, 228, 363, 505, 566],
    [0, 124, 197, 337, 398, 602],
    [0, 125, 192, 406, 509, 562],
    [0, 126, 201, 333, 396, 607],
    [0, 127, 191, 410, 481, 572],
    [0, 128, 232, 370, 507, 564],
    [0, 129, 253, 309, 364, 606],
    [0, 130, 247, 373, 486, 570],
    [0, 131, 240, 315, 362, 611],
    [0, 132, 189, 411, 484, 574],
    [0, 133, 224, 417, 449, 568],
    [0, 134, 328, 397, 458, 553],
    [0, 135, 339, 357, 492, 544],
    [0, 136, 187, 323, 374, 596],
    [0, 137, 286, 383, 502, 552],
    [0, 138, 239, 297, 446, 582],
    [0, 139, 245, 365, 473, 567],
    [0, 140, 218, 330, 369, 604],
    [0, 141, 206, 277, 408, 600],
    [0, 142, 208, 418, 444, 563],
    [0, 143, 288, 409, 462, 548],
    [0, 144, 196, 413, 459, 569],
    [0, 145, 252, 375, 451, 577],
    [0, 146, 249, 298, 455, 590],
    [0, 147, 242, 372, 472, 571],
    [0, 148, 250, 289, 371, 598],
    [0, 149, 212, 326, 367, 609],
    [0, 150, 209, 412, 453, 575],
    [0, 151, 278, 424, 461, 556],
    [0, 152, 195, 302, 501, 594],
    [0, 153, 203, 407, 475, 561],
    [0, 154, 199, 316, 470, 587],
    [0, 155, 217, 312, 457, 588],
    [0, 156, 219, 321, 360, 597],
    [0, 157, 200, 304, 477, 581],
    [0, 158, 213, 274, 403, 603],
    [0, 159, 296, 395, 454, 557],
    [0, 160, 207, 287, 401, 608],
    [0, 161, 279, 377, 490, 558],
    [0, 162, 216, 322, 448, 584],
    [0, 163, 190, 314, 387, 605],
    [0, 164, 202, 290, 482, 583],
    [0, 165, 194, 320, 378, 610],
    [0, 166, 300, 400, 456, 555],
    [0, 167, 221, 284, 386, 601],
    [0, 168, 276, 385, 489, 546],
    [0, 169, 281, 402, 469, 545],
    [0, 193, 303, 419, 480, 534],
    [0, 198, 294, 416, 491, 542],
    [0, 204, 324, 392, 442, 527],
    [0, 205, 282, 421, 483, 533],
    [0, 210, 319, 359, 508, 529],
    [0, 211, 280, 393, 494, 536],
    [0, 214, 335, 358, 487, 528],
    [0, 215, 285, 415, 485, 537],
    [0, 220, 318, 366, 499, 541],
    [0, 222, 338, 368, 465, 540],
    [0, 223, 295, 423, 445, 530],
    [0, 225, 275, 420, 471, 543],
    [0, 229, 273, 376, 497, 539],
    [0, 230, 283, 384, 506, 531],
    [0, 234, 331, 390, 450, 535],
    [0, 236, 336, 361, 460, 538],
    [0, 237, 299, 422, 447, 532],
    [85, 194, 336, 402, 468, 512],
    [85, 195, 311, 419, 474, 517],
    [85, 198, 320, 414, 463, 525],
    [85, 199, 326, 378, 488, 518],
    [85, 200, 333, 392, 466, 524],
    [85, 201, 316, 390, 498, 523],
    [85, 202, 312, 376, 496, 521],
    [85, 205, 273, 391, 493, 510],
    [85, 206, 331, 398, 443, 511],
    [85, 223, 324, 382, 446, 514],
    [85, 231, 334, 383, 455, 522],
    [85, 237, 280, 387, 501, 526],
    [85, 239, 284, 401, 470, 519],
    [85, 240, 302, 397, 457, 520],
    [85, 242, 285, 389, 477, 513],
    [85, 247, 301, 407, 448, 516],
    [85, 249, 287, 375, 482, 515]]

def arrayOrbits : List ((Nat × Nat) × OrbitRecord) := [
  ((17, 2), arrayOrbits0),
  ((18, 3), arrayOrbits1),
  ((77, 12), arrayOrbits2),
  ((102, 17), arrayOrbits3)
]

def fibreOrbits0 : OrbitRecord where
  order := 116
  maps := [[.value (1), .repeat 1 3, .value (-4), .value (6), .repeat 5 84, .value (5), .repeat 91 4, .repeat 1 21]]
  starters := [[0, 1, 2, 3, 4, 109],
    [0, 5, 27, 68, 84, 90],
    [0, 6, 21, 30, 50, 94],
    [0, 7, 28, 58, 62, 106],
    [0, 8, 51, 77, 86, 103],
    [0, 9, 16, 48, 56, 112],
    [0, 10, 15, 37, 78, 91],
    [0, 11, 23, 63, 87, 100],
    [0, 12, 52, 76, 83, 105],
    [0, 13, 38, 57, 67, 107],
    [0, 14, 34, 73, 79, 108],
    [0, 17, 22, 70, 88, 99],
    [0, 18, 24, 36, 41, 102],
    [0, 19, 33, 47, 61, 75],
    [0, 20, 64, 65, 80, 92],
    [0, 25, 49, 59, 81, 93],
    [0, 26, 35, 43, 46, 95],
    [0, 29, 31, 42, 54, 101],
    [0, 32, 39, 55, 85, 98],
    [0, 40, 69, 71, 82, 96],
    [0, 44, 45, 60, 74, 97],
    [0, 53, 66, 72, 89, 104],
    [5, 6, 7, 8, 9, 100],
    [5, 10, 63, 76, 82, 98],
    [5, 11, 28, 33, 81, 97],
    [5, 12, 23, 30, 70, 93],
    [5, 13, 16, 64, 85, 95],
    [5, 14, 41, 48, 69, 99],
    [5, 15, 42, 50, 75, 109],
    [5, 18, 51, 55, 67, 114],
    [5, 19, 22, 25, 73, 110],
    [5, 21, 31, 36, 58, 96],
    [5, 24, 38, 52, 66, 80],
    [5, 29, 39, 61, 74, 105],
    [5, 32, 40, 65, 89, 91],
    [5, 35, 44, 71, 78, 92],
    [5, 37, 45, 83, 87, 113],
    [5, 43, 47, 59, 86, 111],
    [5, 46, 62, 72, 77, 107],
    [10, 11, 12, 13, 14, 96],
    [10, 16, 31, 40, 60, 104],
    [10, 17, 38, 68, 72, 94],
    [10, 19, 26, 58, 66, 115],
    [10, 20, 25, 47, 88, 109],
    [10, 23, 48, 67, 77, 101],
    [10, 24, 44, 83, 89, 106],
    [10, 28, 34, 46, 51, 92],
    [10, 29, 43, 57, 71, 85],
    [10, 36, 45, 53, 56, 110],
    [10, 39, 41, 52, 64, 90],
    [10, 54, 55, 70, 84, 102],
    [15, 16, 17, 18, 19, 90],
    [15, 22, 33, 40, 80, 107],
    [15, 24, 51, 58, 79, 97],
    [15, 25, 52, 60, 85, 96],
    [15, 28, 61, 65, 77, 113],
    [15, 29, 32, 35, 83, 103],
    [15, 31, 41, 46, 68, 105],
    [15, 39, 49, 71, 84, 100],
    [15, 45, 54, 81, 88, 108],
    [15, 56, 72, 82, 87, 101],
    [20, 21, 22, 23, 24, 95],
    [20, 26, 41, 50, 70, 98],
    [20, 27, 48, 78, 82, 104],
    [20, 29, 36, 68, 76, 111],
    [20, 33, 58, 77, 87, 90],
    [20, 38, 44, 56, 61, 108],
    [20, 46, 55, 63, 66, 103],
    [20, 49, 51, 62, 74, 91],
    [25, 26, 27, 28, 29, 91],
    [25, 34, 61, 68, 89, 102],
    [25, 38, 71, 75, 87, 112],
    [25, 41, 51, 56, 78, 100],
    [30, 31, 32, 33, 34, 100],
    [30, 36, 51, 60, 80, 99],
    [30, 39, 46, 78, 86, 114],
    [30, 48, 54, 66, 71, 106],
    [30, 56, 65, 73, 76, 95],
    [30, 59, 61, 72, 84, 109],
    [35, 36, 37, 38, 39, 97],
    [35, 51, 61, 66, 88, 93],
    [40, 41, 42, 43, 44, 93],
    [40, 58, 64, 76, 81, 94],
    [40, 66, 75, 83, 86, 110],
    [45, 46, 47, 48, 49, 90],
    [50, 51, 52, 53, 54, 95],
    [55, 56, 57, 58, 59, 91],
    [60, 61, 62, 63, 64, 101],
    [65, 66, 67, 68, 69, 97],
    [70, 71, 72, 73, 74, 90],
    [75, 76, 77, 78, 79, 93],
    [80, 81, 82, 83, 84, 91],
    [85, 86, 87, 88, 89, 92]]

def fibreOrbits : List ((Nat × Nat × Nat) × OrbitRecord) := [
  ((18, 5, 26), fibreOrbits0)
]

end Lemmata.SteinerSixSpectrum
