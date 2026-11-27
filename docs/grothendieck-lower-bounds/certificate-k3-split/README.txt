The 141 × 321 witness for the real Grothendieck constant of order three

From the root of a checkout, run

  python3 -B docs/grothendieck-lower-bounds/certificate-k3-split/reproduce.py --threads 4

The full replay needs Python 3.9 or later, a C++17 compiler with OpenMP, about
2 GB of RAM and 1 GB of temporary disk. Set --portable to omit CPU-specific
compiler flags. It can take more than one hour. All inputs are local.

The shorter --vectors-only replay checks the 4,309 published near signings,
the bound on their complement assuming list completeness, the attaining
classical assignment, the exact three-dimensional rational vector witness
and the two limits on optimizing this particular construction. The full
replay additionally regenerates the exhaustive list, validates the
symmetry reduction and tail bounds, and checks the enumeration on small games.

The matrix, vectors and attaining signs occur once in the checkout, in
lean/Lemmata/GrothendieckLowerBounds/Data3Split.lean. reproduce.py reads them
with the same parser used for the 81-row witness. second/near-signings.txt has
six unsigned integers per line: the reduced reference score and the five
little-endian 32-bit words of the row-sign mask (a set bit denotes minus).
SHA256SUMS.json identifies the numerical inputs and code actually used by
verify_strongest.py, including the three reconstructed files. proof.txt gives
the mathematical derivation of the search and the bounds. The section on
the enlarged second list and the subsequent sections describe this witness.
