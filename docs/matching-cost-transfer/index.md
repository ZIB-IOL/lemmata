---
title: Positive-cost transfers of matching slack bounds
---

```{include} ../_generated/provenance/matching-cost-transfer.md
```

An additive baseline can change an approximation guarantee substantially.
This entry gives conditions under which positive costs nevertheless retain
a nonnegative-rank lower bound from a shifted violation matrix.
The source lower bound is an explicit input; its proof is outside this entry.

Let $q:I\times J\to\mathbb R$, let $a,b:I\to\mathbb R$, and let
$\alpha>1$. Define

$$
S_{\alpha,a,b}(i,j)
=a_iq(i,j)+b_i-\frac{a_i+b_i}{\alpha}.
$$ (eq-matching-cost-transfer-slack)

If row $i$ has minimum $q(i,j)=1$ and $a_i\geq0$, then $a_i+b_i$
is the minimum of the transformed costs. Under these hypotheses,
$S_{\alpha,a,b}$ is the minimization approximation slack at factor
$\alpha$. The matrix statements below do not silently assume this
optimization interpretation.

Write $r_+(M)$ for nonnegative rank, with value infinity when a matrix has
no finite nonnegative factorization. A factorization of size $k$ expresses
the matrix as a sum of $k$ nonnegative rank-one matrices.

## An exact positive-cost transformation

```{prf:theorem} Positive-cost rank identity
:label: thm-matching-cost-transfer-positive-cost

Let $q:I\times J\to\mathbb R$, $\alpha>1$, and $H>0$.
Set $\gamma=2(\alpha-1)H$. Then
$$
r_+\left(\gamma q+H-\frac{\gamma+H}{\alpha}\right)
=r_+\left(q-\frac1{2\alpha}\right).
$$
The constants on either side are subtracted entrywise.
```

```{prf:proof} of [](#thm-matching-cost-transfer-positive-cost)
:nonumber:

For every entry $q(i,j)$,
$$
H+\gamma q(i,j)-\frac{H+\gamma}{\alpha}
=\gamma\left(q(i,j)-\frac1{2\alpha}\right).
$$
The multiplier $\gamma$ is strictly positive. Multiplication of a matrix
by a positive scalar preserves nonnegative rank, since either factor of
each rank-one summand can be multiplied by the scalar or its reciprocal.
```

```{prf:corollary} Substituting a source lower bound
:label: cor-matching-cost-transfer-source-bound

Under the hypotheses of the preceding theorem, suppose
$$
L\leq r_+\left(q-\frac1{2\alpha}\right),
\qquad L\in\mathbb N.
$$
Every nonnegative factorization of
$\gamma q+H-(\gamma+H)/\alpha$ with $k$ factors satisfies $L\leq k$.
```

```{prf:proof} of [](#cor-matching-cost-transfer-source-bound)
:nonumber:

Apply the rank identity and the upper bound on nonnegative rank supplied
by the given factorization.
```

## A uniform bound on the baseline

```{prf:theorem} Bounded-baseline transfer
:label: thm-matching-cost-transfer-bounded-baseline

Let $q:I\times J\to\mathbb R$, let $a,b:I\to\mathbb R$, and suppose
$$
\alpha>1,\qquad
a_i>0,\qquad
\frac{b_i}{a_i}\leq B\quad(i\in I),\qquad
0\leq B<\frac1{\alpha-1}.
$$
Set
$$
r_0=\frac{1-(\alpha-1)B}{\alpha}.
$$
Then $0<r_0<1$. Every nonnegative factorization of
$S_{\alpha,a,b}$ with $k$ factors yields a nonnegative factorization
of $q-r_0$ with $k+1$ factors.
```

```{prf:proof} of [](#thm-matching-cost-transfer-bounded-baseline)
:nonumber:

Multiply row $i$ of $S_{\alpha,a,b}$ by $1/a_i$, and add the row
constant
$$
d_i=\frac{(\alpha-1)(B-b_i/a_i)}{\alpha}\geq0.
$$
The resulting entry is exactly
$$
\frac{S_{\alpha,a,b}(i,j)}{a_i}+d_i=q(i,j)-r_0.
$$
Positive row scaling does not change the number of factors. The added
matrix has the factorization $d_i\cdot1$, requiring at most one
additional factor. The stated bounds on $B$ give $0<r_0<1$.
```

```{prf:corollary} Transferring a lower bound with one additional factor
:label: cor-matching-cost-transfer-baseline-bound

More generally, assume only $\alpha>1$, $a_i>0$, and $b_i/a_i\leq B$
for every $i$. Define $r_0$ by the same formula.
If $L\in\mathbb N$ and $L\leq r_+(q-r_0)$, every $k$-factor nonnegative factorization of
$S_{\alpha,a,b}$ satisfies $L\leq k+1$.
```

```{prf:proof} of [](#cor-matching-cost-transfer-baseline-bound)
:nonumber:

The row-scaling and row-offset identity remains valid without imposing
the bounds that ensure $0<r_0<1$. It gives a factorization of $q-r_0$
with $k+1$ factors, to which the assumed source lower bound applies.
```

## Positive metric costs and the row minimum

```{prf:proposition} Two-cluster metrics
:label: prop-matching-cost-transfer-metric

Let $V$ be a set, let $s:V\to\{0,1\}$, and let $\gamma\geq0$. Define
$$
c(u,v)=
\begin{cases}
0,&u=v,\\
1,&u\ne v,\ s(u)=s(v),\\
1+\gamma,&s(u)\ne s(v).
\end{cases}
$$
Then $c$ is symmetric, vanishes on the diagonal, is strictly positive
off the diagonal, and satisfies the triangle inequality.
```

```{prf:proof} of [](#prop-matching-cost-transfer-metric)
:nonumber:

Only the triangle inequality needs consideration. If the endpoints lie
in different clusters, every two-edge path between them crosses between
clusters at least once. If the endpoints lie in the same cluster, their
distance is at most one, while every path through a distinct third
vertex has cost at least two. Cases with repeated vertices give equality
or follow from nonnegativity.
```

```{prf:proposition} Transporting a row minimum
:label: prop-matching-cost-transfer-minimum

Let $q:J\to\mathbb R$ satisfy $q(j)\geq1$ for every $j$, with
$q(j_0)=1$ for some $j_0$. If $a\geq0$, then
$$
a q(j)+b\geq a+b\quad(j\in J),
$$
and equality is attained. Thus the transformed costs have minimum $a+b$.
```

```{prf:proof} of [](#prop-matching-cost-transfer-minimum)
:nonumber:

Multiply $q(j)\geq1$ by $a\geq0$, add $b$, and evaluate at $j_0$.
```

## How to instantiate the reduction

For perfect matchings of $K_n$, with $n\geq2$ even, the intended matrix is
$q(U,M)=|M\cap\delta(U)|$, indexed by odd vertex sets $U$ and perfect
matchings $M$. The intended baseline is $H=n/2$, and the edge costs
are $1+\gamma\mathbf1[e\in\delta(U)]$, with
$\gamma=(\alpha-1)n$. The formalized finite-sum identity
`sum_positive_cost` expresses the cost of an edge set as its cardinality
plus $\gamma$ times its number of crossing edges.

To obtain the matching application one must additionally supply the
combinatorial facts that every matching crosses an odd cut at least once
and that a one-crossing matching exists, together with the shifted
matching rank lower bound from
[Braun–Pokutta, *The matching polytope does not admit fully-polynomial
size relaxation schemes*](https://arxiv.org/abs/1403.6710).
These ingredients are not formalized here. The transfer uses a bound for
the **shifted** matrix, rather than merely the exact extension-complexity
lower bound for the unshifted matching slack.

For $V$-joins, the same matching columns may be used after proving the
target optimum separately. For odd-cut minimization, one transposes the
shifted matrix; the supporting theorem `transposed_shift_rank` proves
rank invariance. For odd-red bipartite matching, the algebra applies to
its violation-count matrix once the corresponding minimum and shifted
rank theorem are supplied. The latter parity rank theorem is a separate
dependency; it is not a consequence claimed here of the Braun–Pokutta
matching theorem.

The results concern matrix factorizations. To conclude an LP inequality
lower bound, a formulation-to-factorization theorem or explicit
nonnegative affine certificate must also be supplied.
The [positive-cost LP transfer](#cor-formulation-reduction-positive-cost)
and [bounded-baseline LP transfer](#cor-formulation-reduction-bounded-baseline)
give these conclusions for formulations equipped with explicit certificates.
This separation
follows the reduction viewpoint of
[Braun–Pokutta–Roy, *Strong reductions for extended
formulations*](https://arxiv.org/abs/1512.04932).

## Lean statements and proofs

```{literalinclude} ../../lean/Lemmata/MatchingCostTransfer/Statement.lean
:language: lean
```

```{literalinclude} ../../lean/Lemmata/MatchingCostTransfer/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/matching-cost-transfer.md
```
