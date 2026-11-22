---
title: Exact Bell values and local visibility for the E₈ root correlations
---

```{include} ../_generated/provenance/modified-e8-bell.md
```

The $120\times120$ Bell matrix obtained from the $E_8$ root lines by a
diagonal shift has classical value $6104$. Its vector value is $9240$, so
it gives the ratio $165/109$. For the fixed root measurements, the largest
local visibility is $109/165$, attained by shared relabelings of a
mixture of two sign strategies. The construction and this candidate ratio
appear in @designolle2024better. The missing classical upper bound is
listed as an open problem in @marton2026exact.

The proof below replaces optimization over $2^{120}$ sign vectors by an
integer calculation on $38\,549$ points in a Weyl chamber. The enumeration,
its completeness proof, and the symmetry reduction are included in the
Lean formalization. A separate integer replay accompanies the entry.

## The matrix

Let $v_1,\ldots,v_{120}\in\mathbb R^8$ contain one representative of each
antipodal pair of $E_8$ roots. We use the $56$ vectors $e_i-e_j,e_i+e_j$
with $i<j$, followed by the $64$ vectors

$$
\frac12(1,\varepsilon_2,\ldots,\varepsilon_8),
\qquad \varepsilon_i\in\{-1,1\},\quad
\prod_{i=2}^8\varepsilon_i=1.
$$

Write $V$ for the matrix with these rows and set

$$
U=3VV^{\mathsf T}-13I_{120}.
$$ (eq-modified-e8-bell-matrix)

Changing representatives or their order conjugates $U$ by a signed
permutation and preserves the optimization problems below. The supplied
replay identifies this matrix with
[the published U120 matrix](https://github.com/istvanmarton/IBB/blob/6f17e2f073ccbe2de9cd0a7d062c25bff59ba844/Examples/U120.txt)
of @marton2026exact by checking every entry of an explicit signed permutation.

```{prf:theorem} Exact classical value
:label: thm-modified-e8-bell-classical

For every $a,b\in\{-1,1\}^{120}$,

$$
|a^{\mathsf T}Ub|\le6104.
$$

There are sign vectors attaining equality. Thus the classical value of
$U$ is exactly $6104$.
```

````{prf:proof} of [](#thm-modified-e8-bell-classical)
:nonumber:

Fix $a$ and put $p=V^{\mathsf T}a$. Maximizing over the second signing
gives $\|Ua\|_1$. For $\varepsilon\in\{-1,1\}$ and $x\in\mathbb R$,

$$
|3x-13\varepsilon|+3\varepsilon x
=\max\{13,6\varepsilon x-13\}
\le\max\{13,6|x|-13\}.
$$

Since $\sum_i a_i(v_i\cdot p)=\|p\|^2$, it follows that

$$
\|Ua\|_1\le
F(p):=\sum_{i=1}^{120}\max\{13,6|v_i\cdot p|-13\}-3\|p\|^2.
$$ (eq-modified-e8-bell-envelope)

Every coordinate of $p$ has absolute value at most
$14+64/2=46$. The sum of the chosen representatives is
$(46,12,10,8,6,4,2,0)$. Flipping a sign subtracts twice a root;
consequently $p$ has integer coordinates of a common parity.

Use the simple roots

$$
\tfrac12(1,-1,-1,-1,-1,-1,-1,1),\quad
e_1+e_2,\quad e_2-e_1,\ldots,e_7-e_6.
$$

Their reflections act as simultaneous signed permutations on the two
output lists and preserve the Bell value. Among all pairs with a fixed
Bell value, choose one maximizing $\rho\cdot p$, where
$\rho=(0,1,2,3,4,5,6,23)$. This maximum exists because there are finitely
many output pairs. Each simple root has inner product one with $\rho$.
A negative simple pairing would give a score-preserving reflection
increasing $\rho\cdot p$, a contradiction. We may therefore assume

$$
|p_1|\le p_2\le\cdots\le p_7,
\qquad p_8\ge-p_1+p_2+\cdots+p_7.
$$

There are nonnegative integers $d,s,t,a,b,c,e,f$ such that
$p_1=s-t$, $p_2=s+t$, the five successive differences from
$p_2$ to $p_7$ are $2a,2b,2c,2e,2f$, and

$$
p_8=2d+5s+7t+10a+8b+6c+4e+2f\le46.
$$ (eq-modified-e8-bell-budget)

Conversely, each tuple with this budget reconstructs a chamber point
of common parity. The recursive enumeration lists all such tuples:
at each step it chooses a nonnegative value whose weighted cost fits
the remaining budget. Induction on the remaining weights proves
completeness. Evaluation gives $F(p)\le6104$ at all $38\,549$ points.
This proves the upper bound; changing $b$ to $-b$ gives the bound on
the absolute value.

For attainment, use the following signs in the canonical order above,
with pairs in lexicographic order, the minus root before the plus root,
and half-roots in increasing seven-bit mask order, low bit first.
The digit $1$ denotes $+1$ and $0$ denotes $-1$.

```text
a = 010001011001101101111101110101100110111101111101100100111101110011111101010000001000000011101101111111111000010001101000
b = 011101011001101111111101110101100110111101111001110110111101011011101101000000001000010011111101111111101000000011001000
```

Direct integer evaluation gives $a^{\mathsf T}Ub=6104$.
````

## Vector value

```{prf:theorem} Exact vector value
:label: thm-modified-e8-bell-vector

For every dimension $n$ and unit vectors $x_i,y_j\in\mathbb R^n$,

$$
\left|\sum_{i,j}U_{ij}\langle x_i,y_j\rangle\right|\le9240.
$$

Equality is attained in dimension eight by $x_i=y_i=v_i/\sqrt2$.
```

```{prf:proof} of [](#thm-modified-e8-bell-vector)
:nonumber:

The root frame satisfies $V^{\mathsf T}V=30I_8$ and
$\|v_i\|^2=2$. Thus $U$ has eigenvalue $77$ on the column space of
$V$ and $-13$ on its orthogonal complement. For row stacks $X,Y$
of $120$ unit vectors in any real dimension,

$$
|\operatorname{tr}(X^{\mathsf T}UY)|
\le77\|X\|_F\|Y\|_F=9240.
$$

Taking $X=Y=V/\sqrt2$ attains $9240$ in dimension eight. Therefore
$\mathrm{SDP}_8(U)/\mathrm{L}(U)=9240/6104=165/109$, which implies
$K_G(8)\ge165/109$.

```

## Exact local visibility

Let $P=VV^{\mathsf T}/2$ be the correlations of the normalized roots,
and let

$$
\mathcal C=\operatorname{conv}\{ab^{\mathsf T}:a,b\in\{-1,1\}^{120}\}
$$

be the full bipartite local correlation polytope.

```{prf:theorem} Exact local visibility
:label: thm-modified-e8-bell-visibility

The matrix $(109/165)P$ belongs to $\mathcal C$. Conversely,
$vP\in\mathcal C$ implies $v\le109/165$. In particular, the largest
nonnegative local visibility for these measurements is exactly $109/165$.
```

```{prf:proof} of [](#thm-modified-e8-bell-visibility)
:nonumber:

The upper bound follows from the classical theorem:
$9240v=\langle U,vP\rangle\le6104$.

For the matching local model, the displayed attaining pair has
$a\cdot b=88$. A second pair has $a\cdot b=76$ and Bell value $6104$.
To construct it, put $(y_1,\ldots,y_7)=(e_2,\ldots,e_7,-e_8)$.
Orient the $21$ difference lines as $y_j-y_k$ when
$k-j\pmod 7\in\{1,2,3\}$, and take $y_j+y_k$ on the sum lines.
Orient the remaining lines as $e_1\pm e_j$ and the half-roots with
positive first coordinate. The first player outputs $+1$ on every
oriented line. The second outputs $-1$ on the $21$ differences and on
$h=(e_1-\sum_jy_j)/2$, and $+1$ elsewhere. Transporting these outputs
to the canonical representatives gives the second pair used in Lean.

Choose the trace-$76$ pair with probability $8/11$ and the trace-$88$
pair with probability $3/11$. Then apply seven independent shared
relabelings, chosen uniformly from the explicit lists in the certificate.
The list sizes are $240,126,12,10,8,6,4$. Every relabeling takes a
deterministic pair to another deterministic pair, so every intermediate
average is local.

The certificate retains integer numerators throughout. Starting with
$8a_{76}b_{76}^{\mathsf T}+3a_{88}b_{88}^{\mathsf T}$ and denominator
$11$, each stage sums the relabeled numerators and multiplies the
denominator by its list size. The final denominator is
$D=7\,664\,025\,600$. The finite check verifies, for every pair $i,j$,

$$
1320N_{ij}=109D\,(2v_i\cdot2v_j).
$$

Thus $N/D=(109/165)P$. The Lean proof establishes that this averaging
procedure preserves locality; it does not assume a group order or an
orbit-transitivity statement. Mixing this model with independent fair
outputs gives every visibility between zero and $109/165$. A shared
fair output flip makes all single-party expectations vanish without
changing the correlations.
```

## Reproducibility

The formalization separates the matrix and optimization statements from
the proofs. The chamber domain is explicitly defined, and its completeness is proved
in Lean. Native computation is declared for the finite arithmetic checks;
the generated verification panel lists their statements and dependencies.
The visibility certificate includes all seven lists and an entrywise
integer check. The [visibility replay](replay-visibility.mjs) reads those
same Lean tables and independently checks all entries with Node.js.
The attaining signs and the finite matrix identities used
in the vector proof are also included.

The accompanying [chamber replay](replay-chamber.mjs) and
[published-matrix replay](e8-u120.cjs) also check the eight simple reflections,
coordinate and parity facts, the attaining signs, and the identification
with the published matrix.

From a clone of the repository, run the replays with Node.js 24 or later:

```bash
node docs/modified-e8-bell/replay-chamber.mjs
node docs/modified-e8-bell/replay-visibility.mjs
node docs/modified-e8-bell/e8-u120.cjs --wide --full
```

The visibility replay reads the accompanying Lean source files, so keep
the repository's directory structure. The replays require no packages or
network access. The full formalization and site checks run with
`tools/check.sh` after the setup described in the repository's contributing
instructions.

The published matrix is not redistributed with this entry. The
published-matrix replay regenerates it from the root definition and the
published signed row order, and compares it with
[`Examples/U120.txt`](https://github.com/istvanmarton/IBB/blob/6f17e2f073ccbe2de9cd0a7d062c25bff59ba844/Examples/U120.txt)
at commit `6f17e2f073ccbe2de9cd0a7d062c25bff59ba844`: normalizing the
decimal entries with one space between entries and a final LF on every row
gives $31\,160$ bytes and SHA-256
`70775ad02f460c1d03f9a7144ce322f2864794311e6e72fbe725a485ef631094`.
To check a downloaded copy of that file entry by entry, pass its path as
the first argument of the replay.

```{literalinclude} ../../lean/Lemmata/ModifiedE8Bell/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/modified-e8-bell.md
```
