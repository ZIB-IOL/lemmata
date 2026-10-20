---
title: Nonnegative-rank reductions
---

```{include} ../_generated/provenance/nonnegative-rank-reduction.md
```

Reductions for extended formulations transfer a factorization of a target slack
matrix to a source slack matrix. This entry formalizes the matrix operations
used in [Affine reductions for LPs and SDPs](https://arxiv.org/abs/1410.8816)
and [Strong reductions for extended formulations](https://arxiv.org/abs/1512.04932).
It supplies explicit factors and their sizes. Lower bounds for particular
source matrices are separate inputs.

For a real matrix $M:I\times J\to\mathbb R$, a nonnegative factorization with
$k$ terms consists of nonnegative functions $u_t:I\to\mathbb R$ and
$v_t:J\to\mathbb R$ such that

$$
M(i,j)=\sum_{t=1}^k u_t(i)v_t(j).
$$

Write $r_+(M)$ for the least such $k$, or $\infty$ if no finite factorization
exists. Empty sums are allowed, so the zero matrix has rank zero. The Lean
development reuses the definitions from the
[spanning-tree entry](../spanning-tree-min-split/index.md).
The index sets need not be finite; whenever finiteness of the rank is needed,
it is stated explicitly.

Let $S,A,B:I\times J\to\mathbb R$ and $T:I'\times J'\to\mathbb R$.
Fix maps $f:I\to I'$ and $g:J\to J'$ and assume

$$
S(i,j)=A(i,j)T(f(i),g(j))+B(i,j)
\qquad (i\in I,\ j\in J).
$$ (eq-nonnegative-rank-reduction-identity)

The row map depends only on the row, and the column map only on the column.
The multiplier $A$ and remainder $B$ may depend on both indices; their
factorization sizes measure the cost of this dependence.

```{prf:theorem} Constructive factorization reduction
:label: thm-nonnegative-rank-reduction-factorization

Under the reduction identity, factorizations of $A,T,B$ with respectively
$a,k,b$ terms give a nonnegative factorization of $S$ with $ak+b$ terms.
This holds for every $a,k,b\in\mathbb N$, including zero.
```

```{prf:proof} of [](#thm-nonnegative-rank-reduction-factorization)
:nonumber:

Write
$A(i,j)=\sum_{p=1}^a u_p(i)v_p(j)$ and
$T(i',j')=\sum_{t=1}^k x_t(i')y_t(j')$.
Their contribution to $S$ is

$$
\sum_{p=1}^a\sum_{t=1}^k
\bigl(u_p(i)x_t(f(i))\bigr)
\bigl(v_p(j)y_t(g(j))\bigr).
$$

Each factor is nonnegative. Append the $b$ factors of $B$ to obtain $ak+b$
terms. In Lean, finite sum and product index types are reindexed by
`Fin (a * k + b)`.
```

```{prf:theorem} Nonnegative-rank inequality
:label: thm-nonnegative-rank-reduction-rank

Assume the reduction identity and that each of $A,T,B$ admits a finite
nonnegative factorization. Then

$$
r_+(S)\le r_+(A)\,r_+(T)+r_+(B).
$$

The Lean theorem takes arbitrary finite factorizations of $A,T,B$ as
witnesses of finiteness; they need not have minimum size.
```

```{prf:proof} of [](#thm-nonnegative-rank-reduction-rank)
:nonumber:

A nonempty set of finite factor counts has a least element. Apply the
constructive reduction to minimum-size factorizations of $A,T,B$.
```

```{prf:corollary} Transfer of a lower bound
:label: cor-nonnegative-rank-reduction-lower

Assume the reduction identity and let $L\in\mathbb N$. If every nonnegative
factorization of $S$ has at least $L$ terms, and $A,T,B$ have factorizations
with $a,k,b$ terms, respectively, then

$$
L\le ak+b.
$$

The source lower bound is a hypothesis of this theorem.
```

```{prf:proof} of [](#cor-nonnegative-rank-reduction-lower)
:nonumber:

Apply the source lower bound to the factorization constructed in
[](#thm-nonnegative-rank-reduction-factorization).
```

```{prf:proposition} Transposition
:label: prop-nonnegative-rank-reduction-transpose

For every real matrix $M$, one has $r_+(M^\mathsf T)=r_+(M)$.
```

```{prf:proposition} Positive row scaling
:label: prop-nonnegative-rank-reduction-scaling

For every real matrix $M:I\times J\to\mathbb R$ and function
$c:I\to\mathbb R$ with $c(i)>0$ for every $i$,

$$
r_+\bigl((c(i)M(i,j))_{i,j}\bigr)=r_+(M).
$$

Both invariance statements include the case of infinite rank.
```

```{prf:proof} of [](#prop-nonnegative-rank-reduction-transpose) and [](#prop-nonnegative-rank-reduction-scaling)
:nonumber:

Transposition exchanges the two factors in every summand; transposing again
recovers the original factorization. Row scaling multiplies the row factors
by $c(i)$; scaling by $1/c(i)$ is the inverse construction. Consequently
each operation preserves the set of possible finite factor counts.
```

The implementation also provides pullback, addition, entrywise product, and
nonnegative row-offset constructors. In particular, adding a nonnegative
row-constant matrix needs at most one additional factor. These constructors
can be used without first computing a matrix's nonnegative rank.

The formal statements are separate from their proofs:

```{literalinclude} ../../lean/Lemmata/NonnegativeRankReduction/Statement.lean
:language: lean
```

The exported results are:

```{literalinclude} ../../lean/Lemmata/NonnegativeRankReduction/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/nonnegative-rank-reduction.md
```
