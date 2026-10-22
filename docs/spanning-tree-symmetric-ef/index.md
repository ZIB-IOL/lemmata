---
title: Symmetric formulations of the spanning-tree polytope
---

```{include} ../_generated/provenance/spanning-tree-symmetric-ef.md
```

This entry gives finite theorem statements and Lean formalizations accompanying
Sebastian Pokutta's **“(Approximate) Symmetric Extension Complexity of the
Spanning Tree Polytope.”** See that manuscript for the informal proofs.
The lower-bound argument used here is the Hamilton-path construction; the exact
LP lower bound is its factor-one corollary.

**Scope of the lower bounds.** The LP lower bounds assume the small-index group
theorem stated below. That input is explicit in Lean and is not proved in this
entry. The LP upper formulation, the exact SDP constructions, and the
nonnegative-outer PSD lower bound do not use it.

## Models and conventions

```{prf:definition} Spanning-tree polytope
:label: def-spanning-tree-symmetric-ef-polytope

Let $n\ge2$, let $m=\binom n2$, and let $\mathcal T_n$ be the actual spanning
trees of $K_n$. Write $\chi_T$ for the edge-incidence vector of $T$. The polytope is
$$
P_n=\operatorname{conv}\{\chi_T:T\in\mathcal T_n\}.
$$
```

An LP presentation has an auxiliary real vector space, an affine subspace $A$,
$r$ affine inequalities $a_j(z)\ge0$, and an affine projection $p$. Its image is
$R=p(\{z\in A:a_j(z)\ge0\ \forall j\})$. Equations are free; $r$ counts the
displayed inequalities, including redundant ones. Symmetry means a group
homomorphism from $S_n$ to affine automorphisms of the auxiliary space that
preserve the feasible set and make $p$ equivariant there. The normal-form proof
does not require boundedness, full dimension, or a supplied permutation of rows.

Approximation throughout means **maximization with nonnegative objectives**,
not minimum spanning tree approximation. For $\beta\ge1$, $R$ contains every
$\chi_T$ and satisfies
$$
\langle c,x\rangle\le\beta\max_{T\in\mathcal T_n}\langle c,\chi_T\rangle
\qquad(c\ge0,\ x\in R).
$$

PSD size is the **sum of block orders**, not the number of matrix entries.
A scalar inequality is an order-one PSD block; affine equations are free.
An exact single-cone formulation of order $k$ is an affine slice of
$\mathbb S_+^k$ with a linear projection whose image equals $P_n$.

Lean indexes vectors by `Sym2 (Fin n)`, including diagonal pairs. Tree incidences
are zero on those pairs. `EdgeCoordinates` proves the zero-padding/restriction,
objective, symmetry, and formulation transports from ordinary loopless edges,
without adding LP rows or PSD blocks. PSD slices are written in all real
matrices; positive semidefiniteness itself enforces symmetry.
The actual tree type and unique-path/parent infrastructure are reused from
[the full-slack factorization entry](../spanning-tree-min-split/index.md).

## Hamilton-path LP lower bounds

The explicit input `SmallIndexK3Criterion` is the following group-theoretic
statement: for $n\ge13$, every subgroup $H\le S_n$ with
$[S_n:H]<\binom n3$ contains $A([n]\setminus W)$ for some $|W|\le2$.
Here $A([n]\setminus W)$ consists of the even permutations fixing $W$ pointwise.
The following three statements are conditional on this input.

```{prf:theorem} Finite Hamilton threshold
:label: thm-spanning-tree-symmetric-ef-hamilton

Assume the small-index criterion. Let $n\ge13$. If an affine-symmetric LP
presentation of a $\beta$-approximation has fewer than $\binom n3$ inequalities,
then
$$
\beta\ge\tau_n:=\frac32\left(1-\frac1n\right).
$$
```

```{prf:corollary} Exact LP lower bound
:label: cor-spanning-tree-symmetric-ef-exact-lp

Assume the small-index criterion. For $n\ge13$, every affine-symmetric LP
presentation whose image is exactly $P_n$ has at least $\binom n3$ inequalities.
```

Exactness supplies approximation factor $1$, and $\tau_n>1$ in this range.
Thus no separate finite-gadget proof is needed for this corollary.

```{prf:corollary} Fixed approximation factor
:label: cor-spanning-tree-symmetric-ef-fixed-factor

Assume the small-index criterion. Fix $1\le\beta<3/2$. If
$$
n\ge13\quad\text{and}\quad n>\frac{3}{3-2\beta},
$$
then every affine-symmetric LP presentation of a $\beta$-approximation has at
least $\binom n3$ inequalities.
```

### The construction

For the construction take $n\ge6$ and fix the distinguished vertex labels
$S=\{1,2,3\}$. An ordering $\sigma$ defines
an actual Hamilton path by joining consecutive labels, and a set of distinguished
**positions** $A_\sigma=\{i:\sigma_i\in S\}$. On the auxiliary cycle $C_n$ of
positions, put
$$
\begin{aligned}
k(A)&=\left|E(C_n)\cap\binom A2\right|,\\
w_A&=\frac{3}{n(n-4)}\left(k(A)-\frac4{n-2}\right),\\
\nu_\sigma&=\frac{w_{A_\sigma}}{3!(n-3)!}.
\end{aligned}
$$
These are signed ordering weights, not probabilities. The figure uses one-based
labels and positions; Lean uses `Fin n` and the inverse permutation, sending
labels to positions.

```{figure} ./images/path-certificate.png
:name: fig-spanning-tree-symmetric-ef-path
:alt: Two n=8 examples. On the left, a cycle of positions highlights the three positions occupied by labels 1, 2, and 3. On the right, the corresponding Hamilton path joins consecutive vertex labels. The first ordering has positive weight 1/5760; the second has negative weight -1/11520.
:width: 100%

The Hamilton-path construction from the paper. The auxiliary cycle includes the
dashed closing pair of positions, but the path has no closing edge. In the first
example the cycle count is two while the path has only one edge inside the
triangle of distinguished labels. Reverse orderings give the same undirected
path, so their weights are added. These $n=8$ examples illustrate the
construction, not the $n\ge13$ lower-bound theorem.
```

[Full-size PNG](./images/path-certificate.png) · [PDF](./images/path-certificate.pdf).

## A quadratic-size LP at the threshold

The concrete orientation LP uses variables $y_{ij}$, with
$$
\begin{aligned}
y_{ii}&=0,\\
y_{ij}&\ge0 &&(i\ne j),\\
\sum_j y_{ij}&\le1,\\
y_{ij}+y_{ji}&\le1 &&(i<j),
\end{aligned}
$$
and projection $x_{\{i,j\}}=y_{ij}+y_{ji}$. Vertex permutations act by simultaneous
row and column reindexing.

```{prf:theorem} Symmetric LP with exact factor 3/2
:label: thm-spanning-tree-symmetric-ef-lp-upper

For $n\ge3$, the displayed LP is affine-symmetric, has exactly $3m+n$
inequalities, contains every spanning-tree incidence vector, and is a
$3/2$-approximation. No smaller factor is valid for this same relaxation.
```

```{prf:corollary} Cardinality slice
:label: cor-spanning-tree-symmetric-ef-cardinality

For $n\ge4$, intersecting this relaxation with $\sum_e x_e=n-1$ still gives exact
worst-case approximation factor $3/2$.
```

## Exact quadratic-size semidefinite formulations

The following constructions use a **single PSD cone**, with no extra scalar
inequality blocks or rank constraints. Exactness and symmetry refer to the same
affine slice and projection.

```{prf:theorem} Coordinate-permutation-symmetric formulation
:label: thm-spanning-tree-symmetric-ef-sdp-raw

For $n\ge2$, $P_n$ has an exact PSD formulation of order $3m$ with a coherent
$S_n$-action by simultaneous permutations of matrix rows and columns. The action
preserves the affine slice and feasible set, and the projection is equivariant.
```

```{prf:theorem} Orthogonally symmetric compression
:label: thm-spanning-tree-symmetric-ef-sdp-compressed

For $n\ge2$, $P_n$ has an exact PSD formulation of order $3m-n$. Its coherent
$S_n$-action is by orthogonal congruence $Y\mapsto U_gYU_g^{\mathsf T}$, preserving
the affine slice and feasible set and making the projection equivariant.
```

The compressed action is not asserted to permute coordinates.

```{prf:theorem} Ordered-root formulations
:label: thm-spanning-tree-symmetric-ef-sdp-ordered

For $n\ge2$, $P_n$ has exact PSD formulations of orders $2m$ and $2m-1$.
No symmetry requirement is imposed on these constructions.
```

At $n=2$, these four orders are respectively $3,1,2,1$. The formulas with
subtraction are not being extrapolated to $n=1$.

## A lower bound for nonnegative outer PSD formulations

```{prf:theorem} Sum-of-orders lower bound
:label: thm-spanning-tree-symmetric-ef-psd-lower

Let $n\ge2$. Consider any affine product-PSD presentation with image $R$ such that
$$
P_n\subseteq R\subseteq\mathbb R_{\ge0}^{E(K_n)}.
$$
If its PSD block orders are $k_b$, then
$$
\sum_b k_b\ge\binom{n-1}{2}.
$$
No symmetry, strict-feasibility, or supplied slack-factorization assumption is
required. Singular matrices and zero-order blocks are allowed.
```

The nonnegative-image hypothesis is essential to this statement; it is not being
silently dropped for arbitrary outer relaxations.

## Lean statements

`SymmetricLP` bundles the actual affine presentation and its coherent symmetry.
`HasPermutationPSD` and `HasOrthogonalPSD` bundle the exact formulation, its order,
and the corresponding action on that same formulation. `PSDPresentation` allows
an arbitrary auxiliary space and a finite family of PSD blocks.

```{literalinclude} ../../lean/Lemmata/SpanningTreeSymmetricEF/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

The source separates the Hamilton certificate, affine normal form, concrete LP,
quadratic Gram constructions, and direct product-PSD lower bound into supporting
modules. It does not formalize the small-index input, a minimum-extension-size
operator, or separate asymptotic/optimality claims.

**Reference.** Sebastian Pokutta, *(Approximate) Symmetric Extension Complexity
of the Spanning Tree Polytope*, manuscript. Informal proofs and the construction
illustration are from that work.

```{include} ../_generated/verification/spanning-tree-symmetric-ef.md
```
