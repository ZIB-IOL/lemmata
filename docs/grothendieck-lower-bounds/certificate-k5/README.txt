A rational witness improving the lower bound for K_G(5)

Result: K_G(5) > 1.49936483533988, and therefore the same lower bound for K_G(6).

From a clone of the repository, run
    python docs/grothendieck-lower-bounds/certificate-k5/verify.py

Only the Python standard library is required. The matrix, the vectors and the
attaining signs are stored once, in lean/Lemmata/GrothendieckLowerBounds/Data5.lean,
and read by leandata.py. The program verifies the new five-dimensional rational
vector strategy exactly, as Witness5.lean does in Lean. It checks that the matrix,
written with single spaces and a line feed after every row, has the SHA-256 of
the normalized published matrix recorded in verification.json, and that the
classical assignment attains 919782264. Given a downloaded copy of the
published file as argument, it also compares the two entry by entry.

CLASSICAL UPPER BOUND: imported from Table 4 of Marton, Bene, Divianszky and
Vertesi, Exact classical bounds of bipartite correlation Bell inequalities
using improved branch-and-bound, arXiv:2611.22893 (2026):
    https://arxiv.org/html/2611.22893
That paper gives C(M80x269)=919782264. Its upper-bound computation is not
reproduced by this package. An attaining assignment alone would not establish
the upper bound needed for the Grothendieck lower bound.

The original matrix is Examples/M80x269.txt from
    https://github.com/istvanmarton/IBB
at revision 6f17e2f073ccbe2de9cd0a7d062c25bff59ba844. It is not redistributed
as a file; Data5.lean stores its entries in its own row format. The cited paper
credits Sebastien Designolle for the matrix.

NEW NUMERATOR: the exact rational feasible vector objective is
    1379089182810903048332452323838491520594 / 10^30.
Every vector has five coordinates with common denominator 10^15 and squared
norm at most one. Unit-ball strategies suffice because independently expanding
each vector as a convex combination of antipodal unit vectors expresses the
bilinear objective as an average of unit-vector objectives in the same dimension.

The new vectors were obtained by alternating vector maximization and numerical
polishing. Floating-point optimality is not used: the certificate consists of
the displayed rational vectors and their exactly evaluated objective.

Compared with the cited paper's numerical value 1.3786657706e9, the new feasible
objective is 1.379089182810903048332452323838491520594e9. Thus this is a change in
the vector strategy for the same matrix and classical denominator, rather than
a new classical-bound computation.

Lean (Witness5.lean, Main.lean) proves K_G(5), K_G(6) > 1.49936483533988 from the cited
classical upper bound, stated as a hypothesis for the explicit matrix of Data5.lean.

OPTIONAL FIXED-MATRIX CEILING:
    python verify_ceiling.py

An exact rational semidefinite dual certificate also bounds the best vector
objective of this matrix in every dimension. Write H=[[0,M/2],[M.T/2,0]],
E=diag(y)-H-R.T*R, and eta=max_i sum_j |E_ij|. Then E+eta*I is positive
semidefinite, so sum(y)+349*eta bounds every unit-vector objective. The optional
checker computes this residual using only Python integers and obtains

    Q_infinity(M)/C(M) < 1.49936483534006.

For this upper bound it uses only the attaining classical assignment, not the
paper's classical upper bound. Together with the cited exact classical value,
the gap to the new rational lower witness is less than 1.8e-13. Further vector
optimization on this fixed matrix cannot give a material improvement.
This is not an upper bound on K_G(5), which ranges over all matrices.
