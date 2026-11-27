---
title: Bounds for finite-order Grothendieck constants
---

```{include} ../_generated/provenance/grothendieck-lower-bounds.md
```

An explicit $301\times321$ integer matrix and a rotation argument for the
406-direction local model of Designolle et al. give

$$
1.4397098471655953 < K_G(3) < 1.451263576 .
$$ (eq-grothendieck-lower-bounds-bound)

The lower witness uses rational vectors and an exhaustive classical search.
The upper bound follows by averaging one common rotation of the finite measurement
grid. A stronger upper bound of $1.44705$ has been reported for unpublished work
of Porto et al. For orders five and six we obtain
$K_G(5),K_G(6)>1.49936483533988$ using new
vectors on a matrix with a previously computed classical value. See @designolle2023improved
and @marton2026exact.

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

## The 301-row lower witness

Let $W$ be the matrix in `Data3Orbit.lean`. Starting from the 141 reference
directions, add two neighbors to each direction in a 15-element orbit and to
each direction in a 30-element orbit. Three further orbits, of sizes 10, 30
and 30, place directions at centers of gaps in the intermediate configuration
on the sphere. The search optimizes the matrix coefficients and both players'
vector directions. The resulting integer matrix has 301 Alice settings and
321 Bob settings.

```{prf:lemma} Transport of the sign cutoff
:label: lem-grothendieck-lower-bounds-orbit-transport

If each column of $V$ has absolute sum at most $s$, then
$\|Vu\|_1\le s\|u\|_1$ for every real vector $u$.
```

```{prf:proof} of [](#lem-grothendieck-lower-bounds-orbit-transport)
:nonumber:

The triangle inequality bounds $\sum_i|\sum_k V_{ik}u_k|$ by
$\sum_k |u_k|\sum_i |V_{ik}|\le s\sum_k|u_k|$.
```

Write $C_*=641951269303647081416258863417$.

```{prf:proposition} An attaining column signing
:label: prop-grothendieck-lower-bounds-orbit-attained

There is a Bob signing $b_*$ with $\|Wb_*\|_1=C_*$.
```

```{prf:proof} of [](#prop-grothendieck-lower-bounds-orbit-attained)
:nonumber:

Take the 321 signs in `sOrbitRow`. Integer evaluation of the 301 row sums,
followed by summation of their absolute values, gives $C_*$.
```

```{prf:theorem} A strict order-three bound from 301 settings
:label: thm-grothendieck-lower-bounds-order-three-orbit

For the given $W$, the bound $\|Wb\|_1\le C_*$ for every Bob signing $b$
implies $K_G(3)>1.4397098471655953$.
```

```{prf:proof} of [](#thm-grothendieck-lower-bounds-order-three-orbit)
:nonumber:

The 622 archived triples have integer numerators and common denominator
$D=10^{40}$. Each squared numerator norm is at most $D^2$. The exact vector
score divided by $C_*$ begins $1.4397098471655953648981198686680622\ldots$.
Lean evaluates the integer numerator and proves the strict decimal comparison.
Choosing unit vectors successively in the direction of each player's linear
objective can only increase the score. Since $C(W)=\max_b\|Wb\|_1$, the
hypothesis gives the claimed Grothendieck lower bound.
```

**Classical upper bound.** Let $K$ be the 141-row reference matrix and
$T=641519292$. For any Bob signing with $\|Kb\|_1>T$, take Alice signs $a$
attaining that score. Then $\|K^{\mathsf T}a\|_1\ge a^{\mathsf T}Kb>T$,
so a signed symmetry takes $a$ to one of the 4,309 archived Alice records.
For a listed $a$, put $h=K^{\mathsf T}a$. Starting with the signs of $h$,
flipping signs on a set $J$ costs exactly $2\sum_{j\in J}|h_j|$, including
free flips at zeros. Enumerating every set that leaves the score above $T$
gives exactly 625,968 Bob representatives under the signed symmetries and
global sign reversal.

The new reference is $H=VK$, where the largest absolute column sum of the
integer transport $V$ is $s=984625626$. By
[](#lem-grothendieck-lower-bounds-orbit-transport), every $b$ with
$\|Hb\|_1>sT$ occurs in the preceding list up to symmetry. Exactly 101,967
representatives pass this test. The verifier checks the signed symmetries of
$W$ and evaluates $\|Wb\|_1$ on every retained representative. The largest
value is $C_*$.

For the complement, the reconstruction writes $W=qH+pF$ with
$q=10^{12}$ and $p=999999444607$. It bounds the classical value of $F$ by
$U$, using nonnegative combinations of certified games, signed relabelings,
an integer Gram factor for the perturbation, and the sum of absolute
rounding errors. The resulting exact inequality is

$$
 \|Wb\|_1\le qsT+pU
 = C_*-\frac{3331653634016345743803}{40000000}<C_* .
$$ (eq-grothendieck-lower-bounds-orbit-complement)

This establishes the classical hypothesis of
[](#thm-grothendieck-lower-bounds-order-three-orbit). Together with
[](#prop-grothendieck-lower-bounds-orbit-attained) it gives $C(W)=C_*$.
A separate Gram certificate bounds the gain from changing both sets of
vectors on this particular matrix, even in arbitrary real dimension, by
$7.2\times10^{-35}$ in the ratio. With the displayed directions fixed, the
certificate gives a ceiling of $1.4397119$ for the search using arbitrary
row transports, the specified perturbation bound, 24 comparison groups and
128 listed embeddings. Bhattiprolu and Heinävaara conjecture that
$K_G(3)=1/\ln 2$. The new lower bound is about $0.00298519$ below that
value. See @heinavaara2023research, §3.15.

**Reproduction.** The [computation archive](certificate-k3-301/computation.zip)
contains the proof, matrix, triples, sign lists, solver checkpoints and
independent checkers. In a repository checkout the
[replay script](certificate-k3-301/reproduce.py) first compares the Lean
inputs with the archive, then regenerates both new sign lists and checks
the classical maximum. Run it with Python 3 and a C++17 compiler with OpenMP.

```bash
python3 -B docs/grothendieck-lower-bounds/certificate-k3-301/reproduce.py
```

Add `--from-scratch` to regenerate the 4,309 parent records from the 81-row
base as well. From the extracted archive, the corresponding standalone
command is `python3 -B certificate.py --from-scratch`.

## The 141-row lower witness

Split two orbits of 30 rows of an 81-row integer matrix. For a row $r_i$ in either
orbit the comparison matrix has the pair $r_i+d_i,r_i-d_i$. Each of the other
21 rows becomes $2r_i$. Equal signs on a pair recover the original row, and
opposite signs select its displacement. Optimizing a matrix around this comparison
gives a $141\times321$ integer matrix $M_*$ with 462 rational vector triples.
The triples have common denominator $10^{36}$. Their exact objective is $q_*=N/10^{72}$,
where

$$
\begin{aligned}
N={}&924161982767004923304275072475\cdot 10^{60}\\
 &+569794056604412473073157292179\cdot 10^{30}\\
 &+614339537187061744866701519909.
\end{aligned}
$$

The classical maximum and the witnessed ratio are

$$
C(M_*)=641951276514383746,\qquad
\frac{q_*}{C(M_*)}=1.439613903075240450253037537110037145\ldots .
$$

```{prf:theorem} Order three with 141 rows
:label: thm-grothendieck-lower-bounds-order-three-split

For the matrix $M_*$ in `Data3Split.lean`, the bound
$C(M_*)\le641951276514383746$ implies $K_G(3)>1.4396139030752404$.
```

```{prf:proof} of [](#thm-grothendieck-lower-bounds-order-three-split)
:nonumber:

Direct integer computation gives the stated $N$ and bounds each squared
numerator norm by $10^{72}$. With one player's vectors fixed, each of the
other player's vectors can be taken on the unit sphere by maximizing its
linear objective. Apply this first to the rows and then to the columns.
The resulting unit-vector objective is at least $q_*$. Dividing by the
classical upper bound gives the strict inequality by rational comparison.
```

Here is how the exhaustive computation supplies the hypothesis. Write
$f_K(a)=\|K^{\mathsf T}a\|_1$ for the score on the comparison matrix $K$.
Verified signed symmetries reduce the search on the 21 protected row signs
to 17,504 prefixes. On each prefix a weighted cover bounds the gain from
choosing displacements. The resulting exhaustive search lists 7,832,114
base signings above $314271488$. Starting from these signings and testing
the eligible choices of displacement rows gives 4,309 representatives
covering every signing with $f_K(a)>641519292$. Both matrices respect
the symmetries used in this reduction. The proof of coverage, including
the reverse search on the split rows, is in the [certificate derivation](certificate-k3-split/proof.txt).

For the complementary signings, the checker reconstructs
$M_*=KW+E+\sum_g H_g$. If $t$ is the maximum absolute row sum of $W$,
then $f_{KW}(a)\le t f_K(a)$. An integer Gram factor and a bound on its
residual give a uniform bound on $f_E(a)$ by weighted Cauchy–Schwarz.
The $H_g$ are copies of small games or certified comparison games, with any
integer rounding error included in their bounds. Adding the bounds gives
$f_{M_*}(a)\le641951274320921384$ on the complement. On the 4,309
representatives the exact maximum is $641951276514383746$, and the stored
signing attains it. This proves the stated value of $C(M_*)$.

The [141-row certificate](certificate-k3-split/README.txt) reads the matrix, vectors
and attaining signs from the Lean source. The full replay regenerates the list of
signings. The shorter replay checks the archived list and the remaining arithmetic.

```bash
python3 -B docs/grothendieck-lower-bounds/certificate-k3-split/reproduce.py --threads 4
python3 -B docs/grothendieck-lower-bounds/certificate-k3-split/reproduce.py --vectors-only
```

For this same matrix, a second rational Gram certificate bounds the increase
over $q_*/C(M_*)$ obtainable by reoptimizing *all* vectors, even in arbitrary
real dimension, by $7.31\times10^{-35}$. A separate dual certificate uses the
stored vectors and bounds the ratio obtainable by the specified invariant
matrix search (column contractions, a semidefinite remainder, and the
certified games) by $1.439613934233937$, less than $3.12\times10^{-8}$
above the exhibited ratio. These two estimates describe the limits of the
particular construction. A bound on $K_G(3)$ itself must hold for all matrices.

## A global upper bound from a rotated measurement grid

Designolle et al. construct a finite local model on 406 measurement directions
in $\mathbb S^2$. Changing the outcome sign extends it to the antipodes.
Let $P$ be the convex hull of those signed directions. Their supplement gives
the squared inradius $\eta^2$ and the squared approximation error $\upsilon$ as
exact rationals. The finite-model visibility is $w_{\rm D}=(173/250)/(1+\sqrt{\upsilon})$.
Using the ball of radius $\eta$ on both sides gives
$1/(w_{\rm D}\eta^2)=1.454633656718692947\ldots$ as the upper endpoint.
The authors give the parameters publicly and offer the explicit local decomposition
on request. We use their finite local-model result as an input. See @designolle2023improved,
in particular Eq. (4) and its supplement.

For a polytope $P$ with unit vertices $V\subset\mathbb S^2$, a *finite local model
at visibility $w$* means that $(w\langle u,v\rangle)_{u,v\in V}$ is a convex
combination of matrices of the form $(\varepsilon_u\delta_v)_{u,v\in V}$ with
all signs in $\{\pm1\}$. A common sign change on one side handles the singlet sign.
By independently writing each $p_i,q_j\in P$ as a convex combination of vertices,
every finite real matrix $M$ satisfies

$$
\sum_{ij}M_{ij}\langle p_i,q_j\rangle\le C(M)/w .
$$

Indeed, for each choice of vertices a deterministic assignment to the vertices
induces an assignment to the row and column settings of $M$. Averaging first
over that assignment and then over the vertex choices gives the inequality.

**Rotation bound.** Suppose $0<h<1$, $hB_2^3\subset P\subset B_2^3$, and all
vertices of $P$ have unit length. Let $a=19/20$ and put

$$
 b=\frac{1+h}{2},\qquad \delta=\frac{1-h}{2},\qquad
 r=h+\frac{h^3(1-h)}4,\qquad s=\sqrt{1-2ah+a^2}.
$$

If $\lambda=b^2+a(r-b)-s\delta>0$ and $P$ has a finite local model at
visibility $w>0$, then $K_G(3)\le 1/(w\lambda)$.

*Proof.* Write $h_P(z)=\max_{v\in V}\langle v,z\rangle$ and
$\rho(z)=\max\{t:tz\in P\}$ for unit $z$. Let $\alpha$ and $\beta$ be
their respective averages over the unit sphere with normalized area measure.

First, $\alpha\ge b$. Partition the sphere into the Voronoi cells of the
vertices. Each cell is an intersection of hemispheres and contains its
vertex $v$. All points of the cell have angular distance at most $\arccos h$
from $v$, since $h_P\ge h$. In polar coordinates about $v$, each meridian
therefore meets the cell in an interval $[0,T]$ with $T\le\arccos h$.
On this interval $h_P=\cos\theta$. Its mean with weight $\sin\theta$ equals
$(1+\cos T)/2\ge b$. Integrating over meridians and cells gives the claim.

Second, $\beta\ge r$. Triangulate each facet using its vertices. For one
triangle let $d\ge h$ be its plane's distance from the origin, and measure
planar coordinates $t$ from the perpendicular foot. The vertex coordinates
$t_1,t_2,t_3$ satisfy $\|t_k\|^2=1-d^2$. The mean with respect to uniform
planar area is

$$
 \mathbb E_{\rm area}\|t\|^2=
 \frac{3(1-d^2)+\|t_1+t_2+t_3\|^2}{12}\ge\frac{1-d^2}{4}.
$$

This follows from the barycentric moments $\mathbb E\lambda_i^2=1/6$ and
$\mathbb E\lambda_i\lambda_j=1/12$ for $i\ne j$. The radius
$u=\sqrt{d^2+\|t\|^2}$ lies in $[d,1]$. Radial projection onto the sphere
has area Jacobian $d/u^3$, between $d$ and $d^{-2}$. The mean of $\|t\|^2$
on the spherical patch is therefore at least $d^3(1-d^2)/4$. On this patch
$\rho=u=d+\|t\|^2/(u+d)\ge d+\|t\|^2/(1+d)$.
Its mean is at least $d+d^3(1-d)/4$. This function is increasing on $[0,1]$,
so averaging over all patches proves $\beta\ge r$.

Choose a maximizing family $x_i,y_j\in\mathbb S^2$ for $Q=Q_3(M)$.
Take one Haar-uniform $R\in{\rm SO}(3)$ common to both players. Choose a
maximizing vertex $v(z)$ for $h_P(z)$, breaking ties measurably, and set

$$
 A_R(x)=R^{-1}v(Rx),\qquad B_R(y)=\rho(Ry)y .
$$

Both $R A_R(x)$ and $R B_R(y)$ belong to $P$, so their unrotated bilinear
score is at most $C(M)/w$ for every $R$. Invariance under rotations fixing
$x$ makes $\mathbb E A_R(x)$ parallel to $x$, and its inner product with $x$
is $\alpha$. Likewise $\mathbb E B_R(y)=\beta y$.
The pointwise deviations satisfy

$$
 \|A_R(x)-ax\|^2=1-2a h_P(Rx)+a^2\le s^2,\qquad
 \|B_R(y)-by\|\le\delta .
$$

The bilinear objective on these two families of deviations is at least
$-s\delta Q$ for each $R$. Indeed, after rescaling they lie in the unit balls,
where the maximum absolute objective is $Q$ by linearity in each vector and
a sign change on one side. Expand this residual objective and take expectations.
The identities for the means give

$$
 \frac{C(M)}{w}\ \ge\
 \mathbb E\sum_{ij}M_{ij}\langle A_R(x_i),B_R(y_j)\rangle
 \ \ge\ (b\alpha+a\beta-ab-s\delta) Q
 \ \ge\ \lambda Q .
$$

This holds for every finite $M$. Taking the supremum proves the rotation bound.

```{prf:lemma} Averaging a centered bilinear score
:label: lem-grothendieck-lower-bounds-averaged

Write $F(X,Y)=\sum_{ij}M_{ij}\langle X_i,Y_j\rangle$ and $Q=F(x,y)$.
On any probability space take random vector families $A,B$ for which the
mixed scores $F(A,y)$ and $F(x,B)$ are integrable and have means $\alpha Q$
and $\beta Q$. Suppose pointwise that $F(A,B)\le U$ and
$F(A-ax,B-by)\ge-eQ$. Then $(b\alpha+a\beta-ab-e)Q\le U$.
```

```{prf:proof} of [](#lem-grothendieck-lower-bounds-averaged)
:nonumber:

Expand $F(A-ax,B-by)$ bilinearly to obtain
$bF(A,y)+aF(x,B)\le U+(ab+e)Q$ for every sample. Integrate the two
mixed scores and use their means. In the rotation proof the variables are
bounded and measurable, $e=s\delta$, and $U=C(M)/w$.
```

With $h=0.9967561175483381$ and $w=0.6919401772871383$, the published exact
inputs give $h^2\le\eta^2$ and $w^2\upsilon\le(173/250-w)^2$ with $w<173/250$.
Thus the finite model applies at $w$ (the zero correlation is local).

```{prf:theorem} Uniform numerical upper bound
:label: thm-grothendieck-lower-bounds-order-three-upper

Use these $h,w$ and the constants $a,b,\delta,s,r$ of the rotation bound. Let
$Q=F(x,y)$ be the maximum of the score on the three-dimensional unit balls,
and let $C>0$. Suppose the mixed scores $F(A,y),F(x,B)$ are integrable and
have means $\alpha Q,\beta Q$ with $\alpha\ge b$ and $\beta\ge r$.
If $F(A,B)\le C/w$, $\|A_i-ax_i\|\le s$, and $\|B_j-by_j\|\le\delta$
for every sample and setting, then $Q/C\le1.4512635753$.
```

```{prf:proof} of [](#thm-grothendieck-lower-bounds-order-three-upper)
:nonumber:

Rescale the two deviations by $-1/s$ and $1/\delta$. The resulting vectors
belong to the unit balls, so their score is at most $Q$. Apply the averaging
lemma with $e=s\delta$. Use the rational
$S=9307726176761760540/10^{20}$ and put $\ell=b^2+a(r-b)-S\delta$.
Squaring gives $S\ge s$. Exact rational comparison gives $\ell>0$ and
$1.4512635753\,w\ell\ge1$. Now $\ell Q\le C/w$ implies the result.
```

The rounded grid satisfies these hypotheses with $C=C(M)$ for each nonzero
finite matrix. Its optimal unit-vector score equals its unit-ball optimum
by linearity in each vector. Taking the supremum preserves the uniform
bound $1.4512635753$, which is strictly below $1.451263576$. Hence

$$
 K_G(3)<1.451263576 .
$$ (eq-grothendieck-rotation-upper)

The [exact arithmetic checker](rotation-upper/verify.py) uses integer square roots
and the [three rationals from the supplement](rotation-upper/inputs.json).
Passing the original Julia supplement as an argument also checks the inputs
digit for digit.

```bash
python3 docs/grothendieck-lower-bounds/rotation-upper/verify.py
```

Márton et al. report the stronger global upper bound $K_G(3)\le1.44705$,
attributed to unpublished work of L. E. Porto et al. communicated by
Sébastien Designolle. Their preprint states the bound without its proof.
Taken with the 301-row lower witness, it leaves a gap of about $0.00734015$.
The grid-rotation proof above uses only the older published finite model.
See @marton2026exact and @designolle2023improved.

A global local model reaching the 301-row witness ratio would need visibility
$0.6945843997446660\ldots$. The finite model used here has
$w_{\rm D}=0.6919401772871383\ldots$ even before extending it to all directions.
Improving only the geometric extension factor up to one would therefore
still leave a gap at this witness.

## The earlier 81-row order-three witness

The 81-row matrix $M$ was obtained from the $81\times321$ example of @marton2026exact, see
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
this value, so $C(M)=320975296$ and this witness gives $K_G(3)>1.43888070193021$.

## The 81-row exhaustive classical certificate

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
Its upper bound for the dimension-restricted ratio $K_G(3\mapsto2)$ compares
three-dimensional vector strategies with planar ones. The published local-model
bound for $K_G(3)$ is due to @designolle2023improved.
More recently, @marton2026exact reports the lower bound $1.438746$ from an
$81\times321$ example. The latter paper credits Sébastien Designolle for that
matrix and for the order-five matrix used here. Its order-five lower bound is
$1.498904$, which also applies to order six by monotonicity. The present
witnesses improve these lower bounds. The rotation argument strengthens the
published local-model estimate for order three.

| Order | Previously reported ratio | New rigorous lower bound |
| --- | --- | --- |
| $3$ | $\approx1.438746$ | $>1.4397098471655953$ |
| $5$ | $\approx1.498904$ | $>1.49936483533988$ |
| $6$ | $\approx1.498904$, by monotonicity | $>1.49936483533988$ |

The previous ratios are quoted to the precision reported in @marton2026exact.
The new strict inequalities are obtained by exact rational comparison.

The starting data for order three are `Examples/M81x321.txt` from the
[IBB repository at revision `6f17e2f`](https://github.com/istvanmarton/IBB/tree/6f17e2f073ccbe2de9cd0a7d062c25bff59ba844).
The 81-row witness was found by symmetrizing with signed icosahedral actions,
optimizing the invariant coefficients and three-dimensional vector strategy,
and rounding to integers while preserving the signed symmetries. Numerical
optimization supplies the candidate. The final integer matrix and rational
vectors, rather than numerical optimality or the optimization trajectory,
are the witnesses used in the proof.

For order five, the matrix is `Examples/M80x269.txt` at the same repository
revision. It is used without modification. Its published classical upper-bound
computation remains a cited input to this result.

## Formal scope

Each order-three lower-bound theorem in Lean takes the classical upper bound for its explicit matrix
as its single hypothesis. The data are in `Data3.lean`, `Data3Split.lean` and
`Data3Orbit.lean`. For the 301-row witness the hypothesis ranges over Bob
signings, as in the exhaustive computation. Lean proves the change of signing
convention and the one-norm transport inequality. For orders five and six the hypothesis is the bound
cited from @marton2026exact for the matrix of `Data5.lean`. Lean checks by computation
(`native_decide`, declared in the manifest) that every vector lies in the unit ball, that
the value is the stated rational number, and that the signs attain the classical values;
it proves the passage to unit vectors, the passage from order five to six, the
perturbation lemma and the certificate-reuse theorem. The exhaustive classical computations
for order three use Python and C++. For order five the classical bound comes from
@marton2026exact. For the upper bound, Lean proves the averaging lemma and derives the uniform
numerical ratio from the finite-model score bound, the mixed moments and the two
deviation bounds. The written spherical argument supplies the latter geometric
inputs. The Python checker verifies the radius and visibility against the published
supplement. The finite local model is a cited input, and the fixed-matrix ceilings
are checked separately by exact arithmetic.

```{literalinclude} ../../lean/Lemmata/GrothendieckLowerBounds/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/grothendieck-lower-bounds.md
```
