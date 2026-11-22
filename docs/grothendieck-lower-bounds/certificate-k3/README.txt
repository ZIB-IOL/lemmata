An explicit lower bound for the real Grothendieck constant of order three

Result: K_G(3) > 1.43888070193021.

From a clone of the repository, run

    python docs/grothendieck-lower-bounds/certificate-k3/reproduce.py

The matrix and the vectors are stored once, in
lean/Lemmata/GrothendieckLowerBounds/Data3.lean; leandata.py reads them. The
script writes the matrix (and its rows in the search order, row_order.txt) to a
temporary directory and checks both files against the SHA-256 hashes of the
inputs of the recorded run in provenance.json before the search starts.

Requirements: Python 3.9 or later; g++ with C++17 and OpenMP support.
The default search uses two CPU threads. Choose another count with --threads.
No network access or Python packages are needed. A temporary executable is
compiled from the included source and removed automatically.

The search verifies the row permutation, every supplied signed matrix map,
coverage of all 2^20 normalized protected-prefix assignments, and the tail
bounds, before proving C(M) <= 320975296. It uses only integer arithmetic,
with input bounds checked to prevent overflow. It explores every branch that
is not eliminated by a proven tail bound or a checked symmetry.

The Python check verifies all 402 rational three-dimensional vectors lie in
the Euclidean unit ball, evaluates their objective exactly, checks a sign
assignment attaining 320975296, and compares the quotient with the stated
strict decimal lower bound by rational arithmetic. Lean checks the same facts
(Witness3.lean) and proves that unit-ball vectors can be replaced by unit
vectors without decreasing the value (Sphere.lean).

The optional command

    python reproduce.py --enumerate-near

also enumerates every retained-prefix strategy with value above 319975296,
writing near_strategies.json in the current directory. It produces 15497
strategies with maximum 320975296. These are representatives sufficient for
coverage; they are not asserted to be a list of distinct full group orbits.
It adds a second exhaustive run and prints each retained strategy.

Files:
  row_order.txt          the row permutation used by the search
  leandata.py            reads the matrix and vectors from Data3.lean
  tail_bounds.txt        proposed tail upper bounds, all re-proved by the checker
  symmetry.txt           60 signed maps and 17504 protected-prefix representatives
  verify_classical.cpp   standalone integer branch-and-bound checker
  verify_quantum.py      exact numerator and attaining-strategy arithmetic
  reproduce.py           complete portable reproduction command
  test_verifier.py       small exhaustive-search and malformed-input regressions
  test_oracle_modes.py   exact enumeration/export/symmetry regression tests
  provenance.json        source, construction and fresh verification record
  classical_rerun.log    output of the fresh exact-bound run
  SHA256SUMS.json        hashes of all packaged sources, inputs and logs

Scope: the classical upper bound is a computer-assisted certificate.
Correctness of the C++ program, compiler and runtime are part of its trust
assumptions; it has not been verified in Lean. The Lean development proves
K_G(3) > 1.43888070193021 from this single input, stated for the explicit
matrix of Data3.lean: it checks the vectors and their value and proves the
passage from the unit ball to unit vectors.

Source attribution: the starting 81 by 321 example is M81x321.txt from
https://github.com/istvanmarton/IBB at commit
6f17e2f073ccbe2de9cd0a7d062c25bff59ba844.
The associated paper, arXiv:2611.22893, credits Sebastien Designolle for that
matrix. The current matrix was obtained by signed-icosahedral symmetrization
and subsequent optimization of invariant coefficients and rank-three vectors.
The explicit final integer matrix, not the optimization trajectory, is the
mathematical witness. The included checker was written independently and does
not use source code from IBB.

Optional implementation regressions (after compiling a persistent executable):

    g++ -O3 -std=c++17 -fopenmp verify_classical.cpp -o verify_classical
    python test_verifier.py
    python test_oracle_modes.py

The suites contain 120 and 25 checks, respectively. The first includes rejection
of overflowing integer tokens at end of file; these must never be silently
discarded by a formatted input operation.
