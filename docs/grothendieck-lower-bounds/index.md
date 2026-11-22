---
title: Improved lower bounds for finite-order Grothendieck constants
---

```{include} ../_generated/provenance/grothendieck-lower-bounds.md
```

Explicit rational vector witnesses give the computer-assisted lower bounds

$$
K_G(3)>1.43888070193021,\qquad
K_G(5),K_G(6)>1.49936483533988.
$$ (eq-grothendieck-lower-bounds-bound)

For order three, the matrix is new and its classical maximum is independently
computed by exhaustive integer search. For order five, the matrix is unchanged
from @marton2026exact: the new contribution is an improved vector strategy,
using the classical upper bound proved there. The order-six bound follows by
embedding the five-dimensional vectors. An exact semidefinite dual certificate
also shows that further vector optimization on the order-five matrix can improve
its ratio by less than $1.8\times10^{-13}$.

The accompanying Lean development proves a general certificate-reuse lemma
and numerical implications from explicit hypotheses. The exhaustive C++ search,
Python witness and dual checks, and the cited classical upper bound remain
outside Lean. These scopes are distinguished throughout.

## The constants and the order-three witness

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

The [order-three certificate](certificate-k3.zip) contains an $81\times321$ integer matrix,
the rational vectors, an attaining classical assignment, the checker source,
and a reproduction command. Its matrix has SHA-256 digest

```text
51739169f4c104a1bc98cdc7bd13ac3f652a551af1835c867c49ac8e66ba0822
```

The certificate values are

$$
\begin{aligned}
B=C(M)&=320975296,\\
q&=\frac{461845159210737970564046146266219485493}{10^{30}},\\
\frac{q}{B}&=1.438880701930213254056929497\ldots.
\end{aligned}
$$ (eq-grothendieck-lower-bounds-values)

Every supplied vector has three rational coordinates with denominator $10^{15}$.
The verifier checks its squared norm is at most one using integer arithmetic.
This is sufficient even though $Q_3$ is defined with unit vectors: a vector in
the unit ball is a convex combination of two antipodal unit vectors in the same
space. Expanding these combinations independently expresses the supplied
bilinear objective as an average of feasible unit-vector objectives. Thus
$Q_3(M)\ge q$ without increasing dimension. Combining this with $C(M)=B$
proves the order-three bound in [](#eq-grothendieck-lower-bounds-bound).

```{prf:theorem} Exact order-three implication
:label: thm-grothendieck-lower-bounds-order-three

Let $K,q',c\in\mathbb R$ satisfy

$$
K\ge0,\qquad c\le320975296,\qquad
q'\ge\frac{461845159210737970564046146266219485493}{10^{30}},\qquad
q'\le Kc.
$$

Then $K>143888070193021/10^{14}=1.43888070193021$.
```

```{prf:proof} of [](#thm-grothendieck-lower-bounds-order-three)
:nonumber:

The hypotheses give $q\le q'\le Kc\le K\cdot320975296$. Division by the
positive integer $320975296$ and exact rational comparison prove the assertion.
The certificate supplies these hypotheses for $K=K_G(3)$, $c=C(M)$, and the
explicit vector objective $q'=q$. Supplying the hypotheses is the external
computational part; the Lean theorem proves the implication as stated.
```

## The order-five witness and the order-six bound

For the unchanged $80\times269$ matrix $M_5$ in @marton2026exact, Table 4 gives
$C(M_5)=919782264$. The [order-five certificate](certificate-k5.zip) supplies
349 new five-dimensional rational vectors, again with denominator $10^{15}$
and squared norms at most one. Their exact objective is

$$
q_5=\frac{1379089182810903048332452323838491520594}{10^{30}},
\qquad
\frac{q_5}{919782264}
=1.499364835339881100743264955\ldots.
$$ (eq-grothendieck-lower-bounds-five-values)

The unit-ball argument above gives $Q_5(M_5)\ge q_5$. Together with the cited
classical upper bound, this proves the claimed lower bound on $K_G(5)$.
Appending a zero coordinate preserves all norms and inner products, proving
$K_G(6)\ge K_G(5)$ and the same bound for order six.

The paper reports a vector objective of approximately $1.3786657706\times10^9$
and ratio $1.498904$. The new objective is
$1.379089182810903048332452323838491520594\times10^9$.
The improvement comes from optimizing the vectors with the matrix fixed.
Alternating vector maximization and numerical polishing found the candidate;
only the resulting rational feasibility and objective are needed for the proof.

The checker compares the matrix exactly with the supplied upstream file and
checks an attaining classical assignment. That assignment establishes the
lower bound $C(M_5)\ge919782264$ only. **The classical upper bound is imported
from the cited preprint and is not independently recomputed here.**
The normalized matrix has SHA-256 digest

```text
ac9545ece717e182693d0b2e704060689040a42dbc42da03434dac2b7c6e3554
```

```{prf:theorem} Exact order-five and order-six implication
:label: thm-grothendieck-lower-bounds-orders-five-six

Let $K_5,K_6,q',c\in\mathbb R$ satisfy

$$
0\le K_5\le K_6,\qquad c\le919782264,\qquad
q'\ge\frac{1379089182810903048332452323838491520594}{10^{30}},\qquad
q'\le K_5c.
$$

Then $K_5,K_6>149936483533988/10^{14}=1.49936483533988$.
```

```{prf:proof} of [](#thm-grothendieck-lower-bounds-orders-five-six)
:nonumber:

The hypotheses imply $q_5\le K_5\cdot919782264$. Exact rational comparison
proves the strict lower bound on $K_5$, and $K_5\le K_6$ transfers it to $K_6$.
For the application, take $K_5=K_G(5)$, $K_6=K_G(6)$, $c=C(M_5)$ and $q'=q_5$.
The preceding argument supplies these hypotheses; Lean proves the stated
numerical implication, with monotonicity included explicitly as a hypothesis.
```

## A ceiling for further vector optimization on the same matrix

Write $Q_\infty(M_5)=\sup_d Q_d(M_5)$ and

$$
H=\frac12\begin{pmatrix}0&M_5\\M_5^{\mathsf T}&0\end{pmatrix}.
$$

The order-five archive also contains rational $y\in\mathbb R^{349}$ and
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

```{prf:theorem} Exact fixed-matrix ratio implication
:label: thm-grothendieck-lower-bounds-fixed-matrix

Let $Q,c\in\mathbb R$ satisfy $c\ge919782264$ and
$Q\le689544591405532440504120517535361/500000000000000000000000$.
Then $Q/c<149936483534006/10^{14}=1.49936483534006$.
```

```{prf:proof} of [](#thm-grothendieck-lower-bounds-fixed-matrix)
:nonumber:

Both the denominator lower bound and the comparison constant are positive.
The assertion follows by multiplication and exact rational comparison.
The dual argument above supplies the objective upper bound for
$Q=Q_\infty(M_5)$, and the attaining assignment supplies the denominator
hypothesis for $c=C(M_5)$. These are external inputs to the Lean implication.
```

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
maps. They are not claimed to be distinct full group orbits. The archive's
optional enumeration mode reproduces this set. The numerical bound in the first
section also has a direct full-search certificate and does not depend on a
perturbation argument.

With fixed feasible vectors, the reuse bound gives a linear-programming search:
normalize both branches of the maximum to at most one, preserve the required
symmetries, and maximize the vector objective. Absolute values admit the usual
linear epigraph formulation. After numerical optimization, rationalize the
candidate and evaluate both branches and the numerator exactly. No assertion
that the numerical LP solution is optimal is needed.

## Reproduction and formal scope

Extract [the order-three archive](certificate-k3.zip), enter its `certificate`
directory, and run

```bash
python reproduce.py
```

This requires Python 3.9 or later and a C++17 compiler with OpenMP. It compiles
the included checker, proves the classical upper bound, checks the rational
vectors and an attaining classical assignment, and compares the quotient
exactly. It uses two CPU threads by default and needs no network connection
or Python packages. `--enumerate-near` additionally regenerates the retained
assignments and writes `near_strategies.json` in the current directory.

The supplied tests compare the search with brute force on small instances,
reject incorrect tail bounds and row permutations, check arithmetic limits,
and compare complete near-set enumeration and signed-symmetry coverage with
exhaustive lists. These tests support the implementation; the mathematical
argument for exhaustive coverage and pruning is given above.

For orders five and six, extract [the order-five archive](certificate-k5.zip),
enter its `certificate_d5` directory, and run

```bash
python verify.py
python verify_ceiling.py
```

Both commands use only the Python standard library. The first checks the new
vector witness, matrix identity, attaining classical assignment and strict
quotient comparison. It does not prove the cited classical upper bound.
The second checks the rational dual residual and fixed-matrix ceiling.

The Lean definitions use the actual finite matrix expression
$f_M(a)=\sum_j|\sum_i a_iM_{ij}|$ and the entrywise absolute sum. The theorem
`reuse_classical_certificate` proves the pointwise classical upper bound from
the stated coverage hypothesis. The three numerical theorems prove the exact
implications with all certificate values and inequalities as hypotheses.
They do not establish the concrete C++ search, parse the supplied matrices,
formalize the dual argument, or prove that the Python programs ran correctly.
The numerical results therefore remain computer-assisted, with the C++/Python
implementations, compiler and runtime in their trust assumptions, and the
published order-five classical bound as a cited input. No custom Lean axiom
is used to hide those external computations.

```{literalinclude} ../../lean/Lemmata/GrothendieckLowerBounds/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/grothendieck-lower-bounds.md
```
