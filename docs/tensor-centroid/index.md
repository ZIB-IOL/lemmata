---
title: Maximum Centroid Dimensions of Concise Tensors
---

```{include} ../_generated/provenance/tensor-centroid.md
```

For a tensor $T_{ijk}\in(F^N)^{\otimes3}$ over a field $F$, its **centroid** $\operatorname{Cen}(T)$ consists of triples of linear operators $(X,Y,Z)$ on the three factors such that

$$
\sum_{i'}X_{ii'}T_{i'jk}
=\sum_{j'}Y_{jj'}T_{ij'k}
=\sum_{k'}Z_{kk'}T_{ijk'}
\qquad\text{for all }i,j,k.
$$

A tensor is **concise** if its slices in each direction are linearly independent. Scalar actions always give elements of the centroid. For the diagonal tensor $\sum_{i=1}^N e_i\otimes e_i\otimes e_i$, the centroid has dimension $N$. How large can this dimension be for a concise tensor?

## Previous bounds

@kassabov2026disjoint proved the upper bound $\dim\operatorname{Cen}(T)\le N^{3/2}$ and constructed tensors approaching it asymptotically. They also gave symmetric examples providing the asymptotic lower bound $(\sqrt2/3)N^{3/2}$. We determine the maximum for every $N$ in both cases and prove that this leading constant is optimal in the symmetric case.

## Sharp bounds

The first bound is attained even under a rank restriction. The **rational border rank** $\underline R_F^{\mathrm{rat}}(T)$ is the least $r$ for which a sum of $r$ rank-one tensors over $F(z)$ is regular at $z=0$ and specializes to $T$. Here a rank-one tensor has the form $u\otimes v\otimes w$, and its individual factors may have poles. For a concise tensor in $(F^N)^{\otimes3}$, rational border rank is at least $N$.

::::{prf:theorem} Maximum centroid dimension
:label: thm-tensor-centroid-general

Over any field $F$, every concise tensor $T\in(F^N)^{\otimes3}$ with $N\ge2$ satisfies

$$
\dim\operatorname{Cen}(T)\le q^3+1+
\begin{cases}
s,&s\le1,\\
s(s-1),&2\le s\le q,\\
qs+\max\{0,(s-q-1)^2-q\},&q<s,
\end{cases}
$$

where $q,s$ are the nonnegative integers satisfying $q(q+1)+s=N$ and $s\le2q+1$. The bound is sharp. Moreover, the bound is attained by a concise tensor with the minimum possible rational border rank, namely $N$.

::::

For example, the maximum at $N=6$ is $9$. Symmetry imposes a stronger restriction: a tensor is **symmetric** if it is fixed by every permutation of its three factors. This definition applies over every field, including characteristics two and three.

::::{prf:theorem} Maximum centroid dimension for symmetric tensors
:label: thm-tensor-centroid-symmetric

Over any field $F$, every concise symmetric tensor $T\in(F^N)^{\otimes3}$ with $N\ge2$ satisfies

$$
\dim\operatorname{Cen}(T)\le\binom{q+2}{3}+1+\max\left\{s,\binom{s}{2}\right\},
$$

where $q,s$ are the nonnegative integers satisfying $q(q+3)/2+s=N$ and $s\le q+1$. The bound is sharp.

::::

## Asymptotic maxima

The two formulas give different leading constants for the growth of the maxima.

::::{prf:corollary} Asymptotic maxima
:label: cor-tensor-centroid-asymptotics

Over any field $F$, the maximum centroid dimension of a concise tensor in $(F^N)^{\otimes3}$ is asymptotic to $N^{3/2}$ as $N\to\infty$. For concise symmetric tensors, the maximum is asymptotic to $(\sqrt2/3)N^{3/2}$.

::::

```{literalinclude} ../../lean/Lemmata/Centroid/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/tensor-centroid.md
```
