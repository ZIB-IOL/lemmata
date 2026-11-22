---
title: Improved lower bounds for finite-order Grothendieck constants
---

```{include} ../_generated/provenance/grothendieck-lower-bounds.md
```

An explicit $81\times321$ integer matrix and rational unit-ball vectors in $\mathbb R^3$ give

$$
K_G(3)>1.43888070193021 .
$$ (eq-grothendieck-lower-bounds-bound)

Lean checks the vectors and their value and proves the passage to unit vectors, so the
Lean theorem has one input, the classical value of this explicit matrix. An exhaustive
integer search establishes it; the search is computer-assisted and not formalized. New
vectors for the $80\times269$ matrix of @marton2026exact also give
$K_G(5),K_G(6)>1.49936483533988$ with the classical value computed there.

## The constants

For a nonzero real matrix $M\in\mathbb R^{n\times m}$, write

$$
C(M)=\max_{a\in\{\pm1\}^n,\,b\in\{\pm1\}^m}a^{\mathsf T}Mb
    =\max_{a\in\{\pm1\}^n}\|M^{\mathsf T}a\|_1,
\qquad
Q_d(M)=\max_{u_i,v_j\in\mathbb S^{d-1}}
       \sum_{i,j}M_{ij}\langle u_i,v_j\rangle.
$$ (eq-grothendieck-lower-bounds-definitions)

The real Grothendieck constant of order $d$ is
$K_G(d)=\sup_{n,m,M\ne0}Q_d(M)/C(M)$. The dimension restriction concerns the
real vectors. The unrestricted real and complex Grothendieck constants are
different quantities.

In Lean, $K_G(d)>x$ is stated without the supremum: some matrix with a classical upper bound
$B>0$ has unit vectors in $\mathbb R^d$ whose value exceeds $xB$.

## The order-three witness

The matrix $M$ is new; it was obtained from the $81\times321$ example of @marton2026exact, see
below. It is stored in `Data3.lean` of the Lean source, one row per line, with
$81+321$ rational vectors in $\mathbb R^3$ (numerators over $10^{15}$) and an attaining
classical assignment. Written with single spaces between entries and a line feed after
every row, $M$ has SHA-256 digest

```text
51739169f4c104a1bc98cdc7bd13ac3f652a551af1835c867c49ac8e66ba0822
```

The values are

$$
\begin{aligned}
B=C(M)&=320975296,\\
q&=\frac{461845159210737970564046146266219485493}{10^{30}},\\
\frac{q}{B}&=1.438880701930213254056929497\ldots.
\end{aligned}
$$ (eq-grothendieck-lower-bounds-values)

```{prf:theorem} Order three
:label: thm-grothendieck-lower-bounds-order-three

For the matrix $M$ above, if $C(M)\le320975296$, then $K_G(3)>1.43888070193021$.
```

```{prf:proof} of [](#thm-grothendieck-lower-bounds-order-three)
:nonumber:

Every vector has squared numerators summing to at most $10^{30}$, so it lies in the unit
ball, and the value of the vectors is exactly $q$; Lean checks both by computation. For
fixed column vectors $v_j$ the value is $\sum_i\langle u_i,w_i\rangle$ with
$w_i=\sum_jM_{ij}v_j$, so replacing every $u_i$ by the unit vector in the direction of
$w_i$ does not decrease it, by the Cauchy–Schwarz inequality; the same then holds for the
$v_j$. Hence unit vectors in $\mathbb R^3$ attain at least $q$, and
$q>1.43888070193021\cdot320975296$ by exact rational comparison.
```

The exhaustive search below proves $C(M)\le320975296$, and the signs in the data attain
this value, so $C(M)=320975296$ and [](#eq-grothendieck-lower-bounds-bound) follows.

## The order-three exhaustive classical certificate

Put $f_M(a)=\|M^{\mathsf T}a\|_1$. At a node of the search, let $v$ be the
column-sum vector of the rows already assigned signs. If the remaining rows
have classical value at most $c_k$, every completion has value at most

$$
\|v\|_1+c_k.
$$ (eq-grothendieck-lower-bounds-pruning)

The triangle inequality proves this pruning bound. The checker re-establishes
all supplied tail bounds from shorter tails before using them in the full
search. It also checks that the reordered matrix is an exact row permutation
of the supplied witness. No optimizer output is accepted as a classical upper
bound.

The symmetry certificate supplies 60 signed row-and-column permutations. Each
is checked entry by entry against the integer matrix. They preserve a prefix
of 21 rows. After global sign reversal fixes one prefix sign, the checker
verifies that images of 17,504 retained prefixes cover all $2^{20}$ assignments.
The unrestricted remaining signs are then searched for every retained prefix.
Coverage and invertibility suffice; the checker does not assume group closure.

All partial sums and pruning operations use integer arithmetic, with explicit
range checks. A fixed cutoff avoids reliance on an asynchronously updated
incumbent. The search establishes $C(M)\le320975296$. The supplied sign vector
attains this value, proving equality.

From a clone of the repository, the [order-three certificate](certificate-k3/README.txt) runs
with

```bash
python docs/grothendieck-lower-bounds/certificate-k3/reproduce.py
```

It requires Python 3.9 or later and a C++17 compiler with OpenMP, uses two CPU threads by
default, and needs no network connection or Python packages. It writes the matrix from
`Data3.lean` (and its rows in the search order) to a temporary directory, checks both
against the hashes of the recorded run, compiles the checker, proves the classical upper
bound, and replays the vector checks. `--enumerate-near` additionally regenerates the
retained assignments of the next section. The supplied tests compare the search with
brute force on small instances, reject incorrect tail bounds and row permutations, check
arithmetic limits, and compare complete near-set enumeration and signed-symmetry coverage
with exhaustive lists. These tests support the implementation; the mathematical argument
for exhaustive coverage and pruning is given above.

## Reusing a classical certificate

An exhaustive search can also retain all assignments above a threshold rather
than only certify a maximum. This produces a reusable certificate for nearby
matrices. The following elementary perturbation estimate is the only analytic
ingredient.

For a matrix $D$, write $\|D\|_{\mathrm{ent},1}=\sum_{i,j}|D_{ij}|$.
This denotes the entrywise absolute sum.

```{prf:lemma} Perturbation bound
:label: lem-grothendieck-lower-bounds-perturbation

For real matrices $M_0,Y$ of the same size, $a\in\{\pm1\}^n$, and $t\ge0$,

$$
f_Y(a)\le t f_{M_0}(a)+\|Y-tM_0\|_{\mathrm{ent},1}.
$$
```

```{prf:proof} of [](#lem-grothendieck-lower-bounds-perturbation)
:nonumber:

Apply the triangle inequality to
$Y^{\mathsf T}a=tM_0^{\mathsf T}a+(Y-tM_0)^{\mathsf T}a$ and use
$|a_i|=1$ to bound the second term by the entrywise absolute sum.
```

```{prf:theorem} Reusable classical upper bound
:label: thm-grothendieck-lower-bounds-reuse

Let $M_0,Y\in\mathbb R^{n\times m}$, $T,R\in\mathbb R$, $t\ge0$, and let
$S$ be a finite set of real $n$-vectors. Suppose that:

1. For every sign vector $a$ with $f_{M_0}(a)>T$, there exists a sign vector
   $s\in S$ with $f_Y(a)=f_Y(s)$.
2. $f_Y(s)\le R$ for every $s\in S$.

Then

$$
C(Y)\le\max\left\{R,\ tT+\|Y-tM_0\|_{\mathrm{ent},1}\right\}.
$$ (eq-grothendieck-lower-bounds-reuse)
```

```{prf:proof} of [](#thm-grothendieck-lower-bounds-reuse)
:nonumber:

If $f_{M_0}(a)>T$, the retained representative bounds $f_Y(a)$ by $R$.
Otherwise, [](#lem-grothendieck-lower-bounds-perturbation) and $t\ge0$
bound it by $tT+\|Y-tM_0\|_{\mathrm{ent},1}$. Maximizing over $a$ proves
the assertion. Equality at the threshold belongs to the second case.
```

For a nonempty retained set of sign vectors one may take
$R=\max_{s\in S}f_Y(s)$. If representatives were obtained using signed
symmetries of $M_0$, those maps must preserve $f_Y$ as well. Invariance of
$M_0$ alone does not imply the first hypothesis. A heuristic collection of
near-optimal assignments likewise does not establish coverage.

For the order-three witness, an exhaustive search above $T=319975296$ produces
15,497 retained assignments, sufficient for coverage under the supplied signed
maps. They are not claimed to be distinct full group orbits. The certificate's
optional enumeration mode (`--enumerate-near`) reproduces this set. The numerical bound in the first
section also has a direct full-search certificate and does not depend on a
perturbation argument.

With fixed feasible vectors, the reuse bound gives a linear-programming search:
normalize both branches of the maximum to at most one, preserve the required
symmetries, and maximize the vector objective. Absolute values admit the usual
linear epigraph formulation. After numerical optimization, rationalize the
candidate and evaluate both branches and the numerator exactly. No assertion
that the numerical LP solution is optimal is needed.

## Orders five and six

```{prf:remark} Orders five and six
:label: rem-grothendieck-lower-bounds-orders-five-six

Let $M_5$ be the $80\times269$ matrix of @marton2026exact, credited there to Sébastien
Designolle. New rational vectors in $\mathbb R^5$ have value
$q_5=1379089182810903048332452323838491520594/10^{30}$ on $M_5$. If
$C(M_5)\le919782264$, the classical value computed in @marton2026exact (Table 4), then
$K_G(5),K_G(6)>1.49936483533988$.
```

We do not recompute the classical value: @marton2026exact obtained it with their
branch-and-bound program in about 4.6 days on 64 cores. The new part is the vectors, with
the matrix unchanged: their value improves the reported $q_5\approx1.3786657706\times10^9$
(ratio $1.498904$) to $1.379089182810903\ldots\times10^9$. Lean checks the vectors and their
value as for order three, and appending a zero coordinate gives the bound for order six.
`Data5.lean` stores $M_5$ in its own row format; written with single spaces and a line
feed after every row it has SHA-256
`ac9545ece717e182693d0b2e704060689040a42dbc42da03434dac2b7c6e3554`, the normalized form of
`Examples/M80x269.txt` in the
[IBB repository at revision `6f17e2f`](https://github.com/istvanmarton/IBB/tree/6f17e2f073ccbe2de9cd0a7d062c25bff59ba844).
The [order-five certificate](certificate-k5/README.txt) replays the vector checks with the
Python standard library and, given a downloaded copy of that file, compares the matrices
entry by entry:

```bash
python docs/grothendieck-lower-bounds/certificate-k5/verify.py [M80x269.txt]
```

Further vector optimization on $M_5$ cannot help much. Write $Q_\infty(M_5)=\sup_d Q_d(M_5)$ and

$$
H=\frac12\begin{pmatrix}0&M_5\\M_5^{\mathsf T}&0\end{pmatrix}.
$$

The order-five certificate contains rational $y\in\mathbb R^{349}$ and
$R\in\mathbb R^{349\times349}$. Put

$$
E=\operatorname{diag}(y)-H-R^{\mathsf T}R,\qquad
\eta=\max_i\sum_j|E_{ij}|.
$$

Since $E$ is symmetric, $E+\eta I\succeq0$. Indeed,
$2|x_ix_j|\le x_i^2+x_j^2$ gives
$|x^{\mathsf T}Ex|\le\eta\|x\|^2$.
Consequently $\operatorname{diag}(y+\eta\mathbf1)-H\succeq0$.
For the Gram matrix $X$ of any unit-vector strategy, $X\succeq0$ and
$X_{ii}=1$, so

$$
\langle H,X\rangle\le\sum_i y_i+349\eta
=\frac{689544591405532440504120517535361}{500000000000000000000000}
=:U.
$$ (eq-grothendieck-lower-bounds-dual)

The checker evaluates every entry of $E$ and the displayed upper bound exactly.
An attaining classical assignment gives $C(M_5)\ge919782264$, hence

$$
\frac{Q_\infty(M_5)}{C(M_5)}
\le\frac{U}{919782264}
=1.499364835340057047466878568\ldots
<1.49936483534006.
$$

This upper bound uses only the attaining assignment for its denominator.
Using the cited equality $C(M_5)=919782264$, the gap to the new lower witness
is less than $1.8\times10^{-13}$. A larger improvement requires changing the
matrix. This bounds the ratio for $M_5$ only; it gives no upper bound on any
$K_G(d)$, whose definition ranges over all matrices.

This ceiling is checked by `certificate-k5/verify_ceiling.py` with exact integer arithmetic;
it is not formalized.

## Relation to earlier bounds and matrix construction

@designolle2026better develops finite-order Grothendieck witnesses using
Frank–Wolfe methods and records the order-three lower bound $1.43670$.
The upper bound $K_G(3)\le1.45463$ comes from the local-model construction
in @designolle2023improved.
More recently, @marton2026exact reports the lower bound $1.438746$ from an
$81\times321$ example. The latter paper credits Sébastien Designolle for that
matrix and for the order-five matrix used here. Its order-five lower bound is
$1.498904$, which also applies to order six by monotonicity. The present
witnesses improve these lower bounds and give no new global upper bounds.

| Order | Previously reported ratio | New rigorous lower bound |
| --- | --- | --- |
| $3$ | $\approx1.438746$ | $>1.43888070193021$ |
| $5$ | $\approx1.498904$ | $>1.49936483533988$ |
| $6$ | $\approx1.498904$, by monotonicity | $>1.49936483533988$ |

The previous ratios are quoted to the precision reported in @marton2026exact.
The new strict inequalities are obtained by exact rational comparison.

The starting data for order three are `Examples/M81x321.txt` from the
[IBB repository at revision `6f17e2f`](https://github.com/istvanmarton/IBB/tree/6f17e2f073ccbe2de9cd0a7d062c25bff59ba844).
The new matrix was found by symmetrizing with signed icosahedral actions,
optimizing the invariant coefficients and three-dimensional vector strategy,
and rounding to integers while preserving the signed symmetries. Numerical
optimization supplies the candidate. The final integer matrix and rational
vectors, rather than numerical optimality or the optimization trajectory,
are the witnesses used in the proof.

For order five, the matrix is `Examples/M80x269.txt` at the same repository
revision. It is used without modification. Its published classical upper-bound
computation remains a cited input to this result.

## Formal scope

The Lean theorem for order three takes the classical upper bound for the explicit matrix of
`Data3.lean` as its single hypothesis; for orders five and six the hypothesis is the bound
cited from @marton2026exact for the matrix of `Data5.lean`. Lean checks by computation
(`native_decide`, declared in the manifest) that every vector lies in the unit ball, that
the value is the stated rational number, and that the signs attain the classical values;
it proves the passage to unit vectors, the passage from order five to six, the
perturbation lemma and the certificate-reuse theorem. The exhaustive C++ search for order
three, its compiler and runtime, and the classical value of @marton2026exact remain outside
Lean, as does the ceiling for $M_5$.

```{literalinclude} ../../lean/Lemmata/GrothendieckLowerBounds/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/grothendieck-lower-bounds.md
```
