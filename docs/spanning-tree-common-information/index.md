---
title: A quadratic ceiling for common-information bounds on spanning-tree slack matrices
---

```{include} ../_generated/provenance/spanning-tree-common-information.md
```

Common information cannot supply a superquadratic nonnegative-rank lower bound
when evaluated on the canonical spanning-tree slack matrices below. The
analogous limitation for HSB was already established by Brugger [1]. Here an
entropy bound for unit Boolean factorizations gives an explicit $4n^2$ ceiling
for the **common-information lower-bound quantity**, including all edge
nonnegativity rows.

## Matrices and the ceiling

Use the [full standard slack matrix](#def-spanning-tree-min-split-matrix) from
the spanning-tree factorization entry. Its columns are the actual spanning trees
$T$ of $K_n$ on $V_n=\{0,\ldots,n-1\}$. Its two row families are

$$
 M_n(S,T)=|S|-1-|E(T)\cap\tbinom S2| \quad(2\le |S|<n),
 \qquad M_n(e,T)=\mathbf1_{e\in E(T)} \quad(e\in\tbinom{V_n}{2}).
$$ (eq-spanning-tree-common-information-matrix)

Let $M_n^{\mathrm{sub}}$ be the restriction to the proper subtour rows. The
cardinality equality is not a slack row; the empty, singleton, and full vertex
sets are not included. “Full” means both displayed row families, not an
irredundant facet list.

For a finite nonzero nonnegative matrix, $\mathbb C[M]$ denotes common
information in **bits** after normalizing by its total entry mass. We use
[all finite product seeds](#def-common-information-hsb-ci), not a restricted
rectangle-seed definition.

```{prf:theorem} Full canonical slack
:label: thm-spanning-tree-common-information-full

For every integer $n\ge3$,

$$
 \mathbb C[M_n]\le2\log_2 n+2,
 \qquad 2^{\mathbb C[M_n]}\le4n^2.
$$ (eq-spanning-tree-common-information-full)
```

```{prf:corollary} Subtour rows
:label: cor-spanning-tree-common-information-subtour

For every integer $n\ge3$,

$$
 \mathbb C[M_n^{\mathrm{sub}}]\le2\log_2 n+2,
 \qquad 2^{\mathbb C[M_n^{\mathrm{sub}}]}\le4n^2.
$$ (eq-spanning-tree-common-information-subtour)
```

The second statement is proved for that row restriction, not inferred from a
monotonicity assertion for common information under submatrices.

## A flat-factor entropy bound

```{prf:proposition} Unit rectangle decompositions
:label: prop-spanning-tree-common-information-flat

Suppose a nonzero $a\times b$ matrix is exactly a sum of $k$ unit-weight Boolean
rectangles,

$$
 M=\sum_{z=1}^k \mathbf1_{A_z}\mathbf1_{B_z}^{\mathsf T},
 \qquad Z=\sum_{i,j}M_{ij}>0.
$$ (eq-spanning-tree-common-information-flat)

Then

$$
 \mathbb C[M]\le\log_2\frac{kab}{Z}.
$$ (eq-spanning-tree-common-information-flat-bound)

Empty rectangles are allowed. The indexed family counts duplicate rectangles
with multiplicity.
```

```{prf:proof} of [](#prop-spanning-tree-common-information-flat)
:nonumber:
Put $s_z=|A_z||B_z|$ and $w_z=s_z/Z$. Reveal the rectangle index and then choose
the two coordinates independently and uniformly inside that rectangle. For an
empty rectangle set its weight to zero and use arbitrary probability marginals.
This is one admissible seed in the unrestricted common-information infimum.
Its information cost is

$$
 H_2(M/Z)-\sum_{s_z>0}w_z\log_2s_z
 =H_2(M/Z)-\log_2Z+H_2(w)
 \le\log_2(ab)-\log_2Z+\log_2k.
$$ (eq-spanning-tree-common-information-seed)

The last inequality bounds the two entropies by their alphabet sizes. No
optimality of this particular seed is asserted.
```

Unit weights and Boolean factors are essential. For example, the $1\times1$
matrix $[2]$ has one arbitrary nonnegative rank-one factor and zero common
information, but substituting $a=b=k=1$, $Z=2$ in the proposed bound would give
$\log_2(1/2)<0$. Nor may duplicate unit rectangles be deduplicated while leaving
the matrix and weights unchanged.

## Actual spanning-tree factors and masses

Write

$$
 \Phi_n=\frac{n(n-1)(2n-1)}6.
$$ (eq-spanning-tree-common-information-factors)

```{prf:proposition} Booleanity of the full factorization
:label: prop-spanning-tree-common-information-boolean

For $n\ge3$, the full canonical matrix $M_n$ is a sum of unit Boolean
rectangles on the unchanged published certificate index

$$
 \mathcal C_n=\{(r,v,w):0\le r<v<n,\ r<w<n\},
 \qquad |\mathcal C_n|=\Phi_n.
$$ (eq-spanning-tree-common-information-certificates)
```

```{prf:proof} of [](#prop-spanning-tree-common-information-boolean)
:nonumber:
Reuse the [published full factorization](#prop-spanning-tree-min-split-factorization).
Every column factor is a parent indicator or a reused root-edge indicator.
Every subtour row factor is an indicator, with the reused root-zero diagonal
slots set to zero. For an edge $\{a,b\}$ with $0<a<b$, its two orientation
coefficients occupy distinct slots $(0,a,b)$ and $(0,b,a)$, so their sum never
produces a row coefficient of two. Edges incident to zero use one diagonal
slot. Thus both factors are Boolean, not merely nonnegative, while the already
proved reconstruction and certificate count remain unchanged.
```

The number of rows is

$$
 a_{\mathrm{sub}}=2^n-n-2,
 \qquad a_{\mathrm{full}}=2^n-n-2+\binom n2.
$$ (eq-spanning-tree-common-information-rows)

```{prf:proposition} Constant per-tree column masses
:label: prop-spanning-tree-common-information-masses

For $n\ge3$ and every actual spanning tree $T$ of $K_n$,

$$
 \sum_S M_n^{\mathrm{sub}}(S,T)=(n-3)2^{n-2}+1=:d_{\mathrm{sub}},
 \qquad
 \sum_R M_n(R,T)=(n-3)2^{n-2}+n=:d_{\mathrm{full}}.
$$ (eq-spanning-tree-common-information-masses)
```

```{prf:proof} of [](#prop-spanning-tree-common-information-masses)
:nonumber:
Across the proper nonsingleton subsets, the sum of $|S|$ is
$n2^{n-1}-2n$. Each of the tree's $n-1$ unordered edges lies in exactly
$2^{n-2}-1$ such subsets. Summing $|S|-1-|E(T)\cap\binom S2|$ therefore gives

$$
 n2^{n-1}-2n-(2^n-n-2)-(n-1)(2^{n-2}-1)
 =(n-3)2^{n-2}+1.
$$ (eq-spanning-tree-common-information-counting)

The edge rows contribute exactly $n-1$ more. The formal proof uses the published
parent-edge bijection for actual simple trees and finite subset counting. It
neither assumes an abstract parent model nor uses a formula for the number of
trees.
```

## Completing the bound

```{prf:proof} of [](#thm-spanning-tree-common-information-full) and [](#cor-spanning-tree-common-information-subtour)
:nonumber:
Let $b$ be the number of actual tree columns. This number is finite and positive:
a labelled path supplies a tree. Both column masses $d$ are positive for $n\ge3$.
For either row family, total matrix mass is exactly $bd$. The unit-rectangle
bound therefore cancels the unknown number of trees:

$$
 \mathbb C[M]\le\log_2\frac{\Phi_n a b}{b d}
             =\log_2\frac{\Phi_n a}{d}.
$$ (eq-spanning-tree-common-information-cancellation)

For $n\ge6$, the elementary estimates

$$
 \Phi_n\le n^3/3,\qquad \binom n2\le2^{n-1},\qquad
 a\le3\cdot2^{n-1},\qquad d\ge n2^{n-3}
$$ (eq-spanning-tree-common-information-estimates)

hold for **each** row family, so $\Phi_n a/d\le4n^2$. The remaining cases are
checked exactly from these values:

| $n$ | $\Phi_n$ | $a_{\mathrm{sub}}$ | $d_{\mathrm{sub}}$ | $a_{\mathrm{full}}$ | $d_{\mathrm{full}}$ |
|---:|---:|---:|---:|---:|---:|
| 3 | 5 | 3 | 1 | 6 | 3 |
| 4 | 14 | 10 | 5 | 16 | 8 |
| 5 | 30 | 25 | 17 | 35 | 21 |

Taking logarithms gives $2\log_2n+2$. The real exponential, not a
natural-number power, gives the stated $4n^2$ ceiling.
```

## Meaning and limits

The [rank connection](#prop-common-information-hsb-rank) is
$2^{\mathbb C[M]}\le\operatorname{rank}_+(M)$. Bounding its **left side** above
by $4n^2$ limits the size of the lower bound supplied by this evaluation. It does
**not** bound nonnegative rank or extension complexity above by $4n^2$, and does
not assert tightness of the common-information ceiling.

Brugger [1] already proved $\operatorname{HSB}(S_G)=O(|E(G)|)$ for his canonical
spanning-tree slack matrix of every connected graph $G$. In particular this is
$O(n^2)$ for $K_n$. That published HSB limitation is context, not a new theorem
claimed here or an additional formalization of the arbitrary-graph result.

This entry concerns the two explicitly indexed, unscaled complete-graph matrices.
It makes no upper-bound claim for common information optimized over arbitrary
row/column rescaling, chosen submatrices, conditioning refinements, or other
slack representations. Incomparability of CI and logarithmic HSB does not
transfer either ceiling to the other; the entropy proof above is separate.

```{literalinclude} ../../lean/Lemmata/SpanningTreeCommonInformation/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

## References

1. Matthias Brugger (2021).
   *Limitations of the hyperplane separation technique for bounding the extension complexity of polytopes*.
   Operations Research Letters 49(6), 896–901.
   [DOI](https://doi.org/10.1016/j.orl.2021.11.006).
   [arXiv:1911.01541](https://arxiv.org/abs/1911.01541).

```{include} ../_generated/verification/spanning-tree-common-information.md
```
