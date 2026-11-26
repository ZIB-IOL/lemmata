---
title: "Conditional gradient methods: away-step and fully-corrective Frank–Wolfe"
numbering:
  headings: false
---

```{include} ../_generated/provenance/away-step-frank-wolfe.md
```

:::{note}
This entry comes from the book *Conditional Gradient Methods: From Core Principles to AI
Applications* by Gábor Braun, Alejandro Carderera, Cyrille W. Combettes, Hamed Hassani, Amin
Karbasi, Aryan Mokhtari and Sebastian Pokutta [@braun2025conditional]. It formalizes Sections 2.2.5
and 2.2.6; numbers refer to the arXiv version [@braun2022conditional].
:::

Over a polytope, the Frank–Wolfe algorithm converges only at the rate $O(1/t)$ when the minimizer
lies on a face: the iterates zig-zag between vertices of that face, because the algorithm can only
move toward vertices and never away from them. Away steps [@guelat1986some] remove weight from a
vertex that is currently used, and fully-corrective steps reoptimize over all vertices used so far.
With the pyramidal width of @lacostejulien2015global as the measure of the polytope's geometry,
both variants converge linearly for smooth strongly convex objectives. This entry formalizes
Sections 2.2.5 and 2.2.6 of the book *Conditional Gradient Methods* [@braun2025conditional], in the
numbering of its arXiv version, for a polytope $P = \operatorname{conv} V$ with $V$ a finite set in a
real normed space. The objects are those of [Frank–Wolfe: the core](../frank-wolfe-core/index.md).

## Pyramidal width

For a set $S \subseteq V$ of vertices, a point $x \in \operatorname{conv} S$ and a direction $\psi$,
the *away vertex* $a \in S$ maximizes $\psi$ over $S$, and the *Frank–Wolfe vertex* $v \in V$
minimizes it over $V$.

```{prf:definition} Scaling property and pyramidal width
:label: def-away-step-frank-wolfe-scaling
:nonumber:

The polytope $\operatorname{conv} V$ has the *scaling property* with constant $\delta$ if, for all
such $S$, $x$, $\psi$, $a$, $v$ and every $y \in \operatorname{conv} V$,
$\delta\, \psi(x - y) \le \psi(a - v)\, \|x - y\|$.
```

```{prf:definition} Pyramidal width
:label: def-away-step-frank-wolfe-width
:nonumber:

The *pyramidal width* of $\operatorname{conv} V$ is the supremum of the constants $\delta \ge 0$ with
the scaling property.
```

```{prf:lemma} Scaling inequality via pyramidal width
:label: lem-away-step-frank-wolfe-scaling
:enumerator: 2.26

The pyramidal width has the scaling property: the supremum is attained.
```

```{prf:lemma} Geometric strong convexity
:label: lem-away-step-frank-wolfe-geometric
:enumerator: 2.27

Let $\operatorname{conv} V$ have the scaling property with constant $\delta > 0$, let $f$ be
$\mu$-strongly convex on $\operatorname{conv} V$, and let $x^*$ minimize $f$ there. For an away vertex
$a$ and a Frank–Wolfe vertex $v$ of $f'(x)$,
$f(x) - f(x^*) \le f'(x)(a - v)^2 / (2\mu\delta^2)$.
```

The proof combines the primal gap bound via strong convexity of
[Conditional gradient methods: smoothness, scaling and linear rates](../conditional-gradient-basics/index.md)
with the scaling property at $y = x^*$.

## Facial distance

The pyramidal width is defined by an inequality over all directions. A geometric lower bound comes
from the faces of the polytope, through the polyhedral tools of the core.

```{prf:definition} Facial distance
:label: def-away-step-frank-wolfe-facial
:nonumber:

The facial distance of $\operatorname{conv} V$ is the infimum of $\|p - q\|$ over proper exposed
faces $F$, points $p \in \operatorname{conv} F$ and $q \in \operatorname{conv}(V \setminus F)$.
```

```{prf:proposition} Pyramidal width and facial distance
:label: prop-away-step-frank-wolfe-facial
:enumerator: 2.31

In a finite-dimensional real normed space, the facial distance of $\operatorname{conv} V$ has the
scaling property. Hence the pyramidal width is at least the facial distance, and Theorems 2.29 and
2.34 hold with $\delta$ the facial distance.
```

The book proves equality in Euclidean space; the formal statement is the lower bound, which is the
direction the convergence theorems use. The proof follows the book: by induction on the number of
vertices of $S$ in the minimal face of $y$, pushing $x$ and $y$ away from a common vertex until
either $y$ leaves the face of that vertex or the vertex drops out of the representation of $x$.

## Away-step Frank–Wolfe

The algorithm keeps an active set $S_t \subseteq V$ with weights representing $x_t$. It compares the
Frank–Wolfe gap $f'(x_t)(x_t - v_t)$ with the away gap $f'(x_t)(a_t - x_t)$ and moves toward $v_t$ or
away from $a_t$, whichever is larger, with the short step clipped at the largest feasible step. An
away step that reaches this largest step removes $a_t$ from the active set: a *drop step*.

```{prf:definition} Away-step Frank–Wolfe run
:label: def-away-step-frank-wolfe-afw
:nonumber:

A run starts at a vertex with active set $\{x_0\}$ and weight $1$, and every step is the step of
Algorithm 2.2 with some Frank–Wolfe vertex and some away vertex, with the book's updates of the
weights and the active set. Every tie-breaking rule is allowed.
```

```{prf:theorem} Linear convergence of away-step Frank–Wolfe
:label: thm-away-step-frank-wolfe-afw
:enumerator: 2.29

Let $\operatorname{conv} V$ have the scaling property with constant $\delta > 0$ and diameter $D$,
and let $f$ be convex, $L$-smooth and $\mu$-strongly convex on $\operatorname{conv} V$. Every run
satisfies $f(x_t) - f(x^*) \le (1 - \rho)^{\lfloor (t-1)/2 \rfloor} LD^2/2$ for $t \ge 1$, with
$\rho = \min\{1/2, \mu\delta^2/(4LD^2)\}$.
```

Every step that is not a drop step contracts the primal gap by $1 - \rho$: the chosen gap is at
least half of $f'(x_t)(a_t - v_t)$, and geometric strong convexity bounds the primal gap by its
square. A drop step does not increase the gap. Each Frank–Wolfe step adds at most one vertex to the
active set and each drop step removes one, and active sets are never empty, so drop steps cannot
outnumber the other steps by more than one.

## Fully-corrective Frank–Wolfe

```{prf:definition} Fully-corrective Frank–Wolfe run
:label: def-away-step-frank-wolfe-fcfw
:nonumber:

A run starts at a vertex. Every iterate minimizes $f$ over the convex hull of its active set
$S_t \subseteq V$, and the next iterate is at least as good as every point of the segment from $x_t$
to a Frank–Wolfe vertex, as the minimizer over the convex hull of $S_t \cup \{v_t\}$ in Algorithm 2.3
is.
```

```{prf:theorem} Linear convergence of fully-corrective Frank–Wolfe
:label: thm-away-step-frank-wolfe-fcfw
:enumerator: 2.34

Under the assumptions of Theorem 2.29, every run satisfies
$f(x_t) - f(x^*) \le (1 - \min\{1/2, \mu\delta^2/(LD^2)\})^{t-1} LD^2/2$ for $t \ge 1$.
```

At a minimizer over the convex hull of the active set, every vertex carrying weight has the same
value of $f'(x_t)$, so the away gap vanishes on these vertices and the Frank–Wolfe gap alone
controls the primal gap. There are no drop steps.

:::{note}
**Differences from the book.** The theorems are stated for any constant $\delta > 0$ with the
scaling property, in particular the pyramidal width. In Theorem 2.29 the contraction factor is
$1 - \min\{1/2, \mu\delta^2/(4LD^2)\}$; the book's $1 - \mu\delta^2/(4LD^2)$ is the same whenever
$\mu\delta^2 \le 2LD^2$, which its proof uses. The exponent is $\lfloor (t-1)/2 \rfloor$ instead of
the book's $\lceil (t-1)/2 \rceil$: after the first step the active set can contain two vertices, and
the formal count of drop steps allows one more drop step than good steps.
:::

## Not yet covered

The reverse inequality of Proposition 2.31 (pyramidal width at most the facial distance), the lower
bound of Corollary 2.32 in terms of an inequality description, and the pairwise variant of Section
3.1 are not formalized here.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/AwayStepFW/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/away-step-frank-wolfe.md
```
