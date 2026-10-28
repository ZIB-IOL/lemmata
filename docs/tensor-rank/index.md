---
title: A Square-Root Bound for Asymptotic Tensor Rank
---

```{include} ../_generated/provenance/tensor-rank.md
```

Let $V_1,\ldots,V_k$ be finite-dimensional complex vector spaces. A nonzero tensor of the form $v_1\otimes\cdots\otimes v_k$, with $v_i\in V_i$, is a **rank-one tensor**. The **rank** of $T\in V_1\otimes\cdots\otimes V_k$ is the minimum number of rank-one tensors whose sum is $T$:

$$
R(T)=\min\left\{r\in\mathbb Z_{\ge0}:T=\sum_{a=1}^r v_{1,a}\otimes\cdots\otimes v_{k,a},\quad v_{i,a}\in V_i\right\}.
$$

The empty sum gives $R(0)=0$. The **asymptotic rank** of $T$ is

$$
\widetilde R(T)=\lim_{m\to\infty}R(T^{\otimes m})^{1/m}.
$$

Here $T^{\otimes m}\in V_1^{\otimes m}\otimes\cdots\otimes V_k^{\otimes m}$: factors belonging to the same party are grouped together. Submultiplicativity of rank ensures that the limit exists.

## Previous bounds

For $k\ge4$, @brand2026beyond proved that every $T\in(\mathbb C^n)^{\otimes k}$ satisfies $\widetilde R(T)\le n^{0.772318(k-1)}$. Their general bound in terms of the matrix multiplication exponent $\omega$ is

$$
\widetilde R(T)\le n^{(k-1)\omega/3}.
$$

Combining this with the $\omega\le9/4$ bound of @openai2026upper gives $\widetilde R(T)\le n^{3(k-1)/4}$.

## The square-root bound

We improve the exponent to $k/2$ for every $k\ge4$ and obtain a bound for arbitrary dimensions. Our proof extends the shared-leg separation technique from OpenAI's preprint to the multipartite setting.

::::{prf:theorem} Square-root bound
:label: thm-tensor-rank-square-root-main

For every nonempty finite set of parties $I$, finite-dimensional complex spaces $(V_i)_{i\in I}$, and tensor $T\in\bigotimes_{i\in I}V_i$,

$$
\widetilde R(T)\le\sqrt{\prod_{i\in I}\dim V_i}.
$$

In particular, for integers $k\ge1$ and $n\ge0$, every $T\in(\mathbb C^n)^{\otimes k}$ satisfies $\widetilde R(T)\le n^{k/2}$.

::::

The bound is optimal for every even number of parties.

::::{prf:theorem} Sharpness in even cubical format
:label: thm-tensor-rank-square-root-maximum

For every even integer $k\ge2$ and integer $n\ge0$,

$$
\max_{T\in(\mathbb C^n)^{\otimes k}}\widetilde R(T)=n^{k/2}.
$$

Moreover, every $T\in(\mathbb C^n)^{\otimes k}$ whose $n^{k/2}\times n^{k/2}$ matrix flattening, grouping the first $k/2$ parties as row indices and the last $k/2$ as column indices, is nonsingular satisfies $\widetilde R(T)=n^{k/2}$.

::::

Complete-graph tensors are the starting point of the proof: we first bound their asymptotic rank and then deduce the square-root bound for arbitrary tensor formats.

## Complete-graph tensors

Place a pairing $\sum_{a=1}^d e_a\otimes e_a$ on each edge of the complete graph $K_k$, then group the factors incident with each vertex. Write $G_k(d)$ for the resulting $k$-party tensor. Each local space has dimension $d^{k-1}$, so $d$ is the edge dimension. For $k\ge2$ and $d\ge2$, define its asymptotic rank exponent per edge by

$$
\tau(K_k)=\frac{\log\widetilde R(G_k(d))}{\binom{k}{2}\log d}.
$$

This quantity is independent of $d$. For $k=3$, the tensor is the matrix multiplication tensor and $\tau(K_3)=\omega/3\ge2/3$. @christandl2019asymptotic asked whether $\tau(K_k)<2/3$ is possible for some $k\ge5$ (Question 1.3.1). The case $K_5$ is the first for which the cut lower bound permits such an improvement.

For complete-graph tensors, our method gives

$$
\tau(K_k)\le\frac{k}{2(k-1)}\qquad(k\ge2),
$$

with equality for even $k$. In particular, $\tau(K_5)\le5/8<2/3$, answering their question already for $K_5$.

::::{prf:theorem} Complete-graph bounds
:label: thm-tensor-rank-square-root-graphs

For integers $k\ge2$ and $d\ge1$,

$$
d^{\lfloor k^2/4\rfloor}\le\widetilde R(G_k(d))\le d^{k^2/4}.
$$

If $k$ is even, then $\widetilde R(G_k(d))=d^{k^2/4}$.

::::

It would be interesting to extend this approach to other graph tensors.

```{literalinclude} ../../lean/Lemmata/TensorRank/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/tensor-rank.md
```
