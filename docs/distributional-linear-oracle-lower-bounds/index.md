---
title: Distributional lower bounds for randomized linear-oracle optimization
---

```{include} ../_generated/provenance/distributional-linear-oracle-lower-bounds.md
```

This entry formalizes Theorems 2.7 and 2.9, their fixed-instance consequences,
and Corollary 2.10 of *Lower Bounds for Randomized Linear-Oracle Optimization
over Strongly Convex Sets*. The paper linked above contains the proofs.
The two main bounds are combined in one formal statement. 

## Family and oracle

Fix a query budget $T\in\mathbb N_0$ and positive scales $L,\alpha$. Put

$$
\begin{gathered}
d=64(T+1),\qquad C=(d^2+d+2)^{-1/2},\\
w_k=C\sqrt{2k}\quad(1\le k\le d).
\end{gathered}
$$

For a permutation $\pi$ of $\{1,\ldots,d\}$ define the
family of @grimmer2026lower

$$
S_\pi=\left\{x\in\mathbb R^d:
\frac12\|x\|_2^2+\sum_{i=1}^d w_{\pi(i)}|x_i|\le C^2\right\},
\qquad \widetilde S_\pi=\alpha^{-1}S_\pi.
$$

Choose $\rho\in(0,1)$ as the unique solution of

$$
\sum_{k=1}^d\left[\frac12\rho^2(w_d-w_k)^2+
\rho w_k(w_d-w_k)\right]=C^2.
$$

Set $M=\rho w_d/(1-\rho)$ and use the common known objective

$$
\widetilde f(x)=\frac{L}{2\alpha^2}\|\alpha x-M\mathbf 1\|_2^2.
$$

The feasible sets are $\alpha$-strongly convex in the convention that the ball
of radius $\frac\alpha2\theta(1-\theta)\|x-y\|_2^2$, centered at
$\theta x+(1-\theta)y$, lies in the set for feasible $x,y$ and $0\le\theta\le1$.
The objective is both $L$-smooth and $L$-strongly convex. Write

$$
\begin{gathered}
D=\operatorname{diam}(\widetilde S_\pi)=\frac{2C(2-\sqrt2)}{\alpha},\\
c=\frac{3+2\sqrt2}{6144\cdot64^2},\qquad
b_T=\frac{cLD^2}{(T+1)^2}.
\end{gathered}
$$

Only the permutation is hidden. It is sampled once from the uniform prior,
independently of the method's seed $U$, whose law may be any probability measure
on a measurable space. A paired query $(x,p)\in\mathbb R^d\times\mathbb R^d$
returns the objective value, gradient, and an exact minimizer of
$\langle p,z\rangle$ over $\widetilde S_\pi$; the zero-direction answer is $0$.
Directions are unrestricted, with no span or convex-hull constraint on the method.
Queries, stopping decisions and outputs are measurable functions of the seed and
full query/answer history. Every returned output must be feasible on **every
instance and every seed**, not only almost surely.

Let $N_\pi(U)$ count paired calls up to the first return, with $N_\pi(U)=\infty$
on nontermination. Let $G_\pi(U)$ denote the objective gap of the returned point.
The formal model makes the output total by assigning $0$ on nontermination;
this point is feasible in every set and does not change returned-output events.
The minimum objective value is the same for every permutation.

## Distributional bounds

```{prf:theorem} Expected error and same-threshold probability
:label: thm-distributional-linear-oracle-lower-bounds-main

For any method in the model above with $N_\pi(u)\le T$ for every permutation
and every seed,

$$
\begin{gathered}
\mathbb E_{\Pi,U}G_\Pi(U)\ge b_T,\\
\mathbb P_{\Pi,U}\{G_\Pi(U)\ge b_T\}\ge\frac34.
\end{gathered}
$$

The permutation prior is fixed before the independent seed is drawn and is not
chosen in response to queries. These are Theorems 2.7 and 2.9 of the paper,
packaged together; the formal statement additionally includes $T=0$.
```

## Fixed-instance consequences

```{prf:corollary} Hard instances independent of the realized seed
:label: cor-distributional-linear-oracle-lower-bounds-fixed

Under the hypotheses of [](#thm-distributional-linear-oracle-lower-bounds-main),
there exist permutations $\pi_E$ and $\pi_P$ such that

$$
\begin{gathered}
\mathbb E_U G_{\pi_E}(U)\ge b_T,\\
\mathbb P_U\{G_{\pi_P}(U)\ge b_T\}\ge\frac34.
\end{gathered}
$$

The two witnesses may differ. Each may depend on the randomized method, but
neither depends on its realized seed. These are the fixed-instance conclusions
of Theorems 2.7 and 2.9.
```

The formal fixed-instance and stopping statements use the equivalent threshold
$(L/\alpha^2)C^2/(768d^2)$, named `scaledThreshold` in the source.

## First-return stopping time

```{prf:corollary} Stopping-time tail
:label: cor-distributional-linear-oracle-lower-bounds-stopping

Consider a method with no imposed call cap, measurable at every finite horizon
and with every returned output feasible on every instance and seed. Suppose
$0\le\eta<3/4$ and, for each permutation $\pi$,

$$
\mathbb P_U\!\left\{\begin{array}{l}
N_\pi(U)<\infty\\
\text{and }G_\pi(U)\ge b_T
\end{array}\right\}\le\eta.
$$

Then some fixed permutation $\pi$ satisfies

$$
\mathbb P_U\{N_\pi(U)>T\}\ge\frac34-\eta.
$$

Nontermination belongs to the tail. This is Corollary 2.10 of the paper.
The Lean statement allows any real $\eta$; the range above is the meaningful
probability regime, not an additional formal proof assumption.
```

## Scope

The dimension grows with $T$. Moreover, $\alpha D=2C(2-\sqrt2)$ couples
curvature and diameter in this family: these are not independently prescribed
geometric parameters. The statements do not assert an infinite-time obstruction
in a fixed dimension or a lower bound on practical running time. The construction
of @grimmer2026lower is reused; the contribution covered here is the fixed-prior result
for unrestricted randomized methods and its consequences, from @pokutta2026lower.
Related lower bounds for Frank–Wolfe on strongly convex sets are in
@halbey2026lower and @halbey2026curvature.

```{include} ../_generated/verification/distributional-linear-oracle-lower-bounds.md
```
