---
title: Nonnegative rank of the spanning-tree slack matrix
---

```{include} ../_generated/provenance/spanning-tree-min-split.md
```

A minimum-root decomposition of tree slacks can also accommodate every edge
nonnegativity row without adding factors. This gives an explicit cubic upper bound
on nonnegative rank, saving $\binom n2$ factors over appending a separate factor for
every edge. No symmetry of the factorization is required.

## The matrix and the result

```{prf:definition} Full standard spanning-tree slack matrix
:label: def-spanning-tree-min-split-matrix

Let $V_n=\{0,\ldots,n-1\}$ and $E_n=\binom{V_n}{2}$. Columns are the actual
spanning trees $T$ of $K_n$. Rows are the disjoint union of the sets
$S\subseteq V_n$ with $2\le |S|<n$ and the edges $e\in E_n$. Define

$$
 M_n(S,T)=|S|-1-|E(T)\cap\tbinom S2|,
 \qquad M_n(e,T)=\mathbf 1_{e\in E(T)}.
$$ (eq-spanning-tree-min-split-matrix)

These are the subtour and nonnegativity slacks. The cardinality equality is not a
slack row. “Full” refers to both families of rows, not to an irredundant facet list.
```

Nonnegative rank is the smallest inner dimension of a factorization $M=AB$ with
$A,B$ entrywise nonnegative. The Lean definition uses extended natural numbers,
assigning infinity if no such factorization exists; the explicit witness below
makes the rank finite here.

```{prf:theorem} Full-slack nonnegative-rank bound
:label: thm-spanning-tree-min-split

For every integer $n\ge3$,

$$
 \operatorname{rank}_{+}(M_n)\le \frac{n(n-1)(2n-1)}6.
$$ (eq-spanning-tree-min-split-bound)
```

```{prf:proposition} Explicit factorization
:label: prop-spanning-tree-min-split-factorization

For $n\ge3$, there exist entrywise nonnegative real matrices $A,B$ of inner dimension
$n(n-1)(2n-1)/6$ such that $M_n=AB$.
```

## Construction and proof

For a tree rooted at $r$, let $p_{T,r}(v)$ be the neighbor of $v$ toward $r$, with
$p_{T,r}(r)=r$. For every $r\in S$,

$$
 |S|-1-|E(T)\cap\tbinom S2|
   =\sum_{v\in S\setminus\{r\}}\mathbf1_{p_{T,r}(v)\notin S}.
$$ (eq-spanning-tree-min-split-parents)

Indeed, the parent-edge map bijects the nonroot vertices with the tree edges.
The internal edges of $S$ correspond precisely to the children in $S\setminus\{r\}$
whose parents are also in $S$. Subtracting their number from $|S|-1$ gives the
identity, including when the induced forest on $S$ is disconnected.

Index the factors by

$$
 \mathcal C_n=\{(r,v,w):0\le r<v<n,\ r<w<n\}.
$$ (eq-spanning-tree-min-split-certificates)

The diagonal slots $(0,v,v)$ are special: put
$B_{(0,v,v),T}=\mathbf1_{\{0,v\}\in E(T)}$ and $A_{S,(0,v,v)}=0$
for every subtour row. For every other slot $c=(r,v,w)$, put

$$
 B_{c,T}=\begin{cases}
   \mathbf1_{p_{T,r}(v)<r},&w=v,\\
   \mathbf1_{p_{T,r}(v)=w},&w\ne v,
 \end{cases}
 \qquad
 A_{S,c}=\mathbf1_{\min S=r}\mathbf1_{v\in S}
          \mathbf1_{\,w=v\ \text{or}\ w\notin S}.
$$ (eq-spanning-tree-min-split-factors)

For an edge row $\{a,b\}$ with $a<b$, its row factor is one at $(0,b,b)$ if $a=0$;
if $a>0$, it is one at the two slots $(0,a,b)$ and $(0,b,a)$. All its other
coefficients are zero.

```{prf:proof}
All factors are nonnegative. For a subtour row, only the root $r=\min S$ contributes.
If the parent of $v\in S\setminus\{r\}$ lies below $r$, it is outside $S$ and the
diagonal slot $(r,v,v)$ fires. If it lies above $r$ and outside $S$, exactly the slot
$(r,v,p_{T,r}(v))$ fires. A parent in $S$ contributes nothing. At $r=0$, a parent below
the root is impossible, so replacing those zero column factors by root-edge
incidences preserves the subtour entries **provided their subtour row coefficients
are set to zero**, as above. Thus the parent identity proves every subtour entry.

For an edge row with $a,b>0$, exactly one parent orientation occurs when the edge
belongs to the tree, and neither occurs otherwise:

$$
 \mathbf1_{\{a,b\}\in E(T)}
   =\mathbf1_{p_{T,0}(a)=b}+\mathbf1_{p_{T,0}(b)=a}.
$$ (eq-spanning-tree-min-split-edge-reuse)

The two selected existing factors reproduce that row. An edge incident to zero is
represented by its repurposed diagonal slot. Hence $M_n=AB$ on **both** row families.

Finally,

$$
 |\mathcal C_n|=\sum_{r=0}^{n-1}(n-1-r)^2
               =\frac{n(n-1)(2n-1)}6.
$$ (eq-spanning-tree-min-split-count)

The displayed factorization proves the nonnegative-rank bound.
```

This remains cubic, with leading term $n^3/3$. The saving relative to the older
append-every-edge count is

$$
 \frac{n^3-n}{3}-\frac{n(n-1)(2n-1)}6=\binom n2.
$$ (eq-spanning-tree-min-split-saving)

## Scope and source

The formalization constructs parents from unique paths in actual `SimpleGraph`
trees, proves the parent-edge bijection and slack identity, and checks both row
families. It does not assume an abstract tree-model correctness interface. The
connection between nonnegative rank and extension complexity, an affine extended
formulation, and completeness of a polyhedral description are outside this entry.
No optimality or literature-priority claim is made.

The construction comes from Sebastian Pokutta's spanning-tree extension-complexity
project: the unpublished note *Candidate upper improvement by reusing full-slack
factors* and the earlier min-split factorization. The source snapshot is commit
`75f45e8dd38eae648222e11a99559ed8ec991e2e` of `symmetric-spanning-tree-lb`.
The graph lemmas adapt that project's unique-path and parent-edge proofs. These
source notes are not distributed with this entry; the construction and proofs
needed here are given in full. The entry is self-contained over the archive's
pinned Mathlib and does not import the source project.

```{literalinclude} ../../lean/Lemmata/SpanningTreeMinSplit/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/spanning-tree-min-split.md
```
