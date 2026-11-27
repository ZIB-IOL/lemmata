---
title: "Conditional gradient methods: away-step, fully-corrective and pairwise Frank–Wolfe"
numbering:
  headings: false
---

```{include} ../_generated/provenance/away-step-frank-wolfe.md
```

:::{note}
This entry comes from the book *Conditional Gradient Methods: From Core Principles to AI
Applications* by Gábor Braun, Alejandro Carderera, Cyrille W. Combettes, Hamed Hassani, Amin
Karbasi, Aryan Mokhtari and Sebastian Pokutta [@braun2025conditional]. It formalizes Sections 2.2.4,
2.2.5 and 3.1.1; numbers refer to the arXiv version [@braun2022conditional].
:::

:::{admonition} Errata
:class: warning

**Corollary 2.32.** The book bounds the pyramidal width by $\min \|b_I - A_I v\| / \|A_I\|$ and
justifies it by saying that this fraction bounds the distance between the face
$F = \{A_I z = b_I\}$ and the convex hull of the other vertices. That holds for each vertex but
not for their convex hull: in the triangle with vertices $(0,0)$, $(1,0)$, $(0,1)$ and the rows
$-y \le 0$, $-x \le 0$, $x + y \le 1$, the face $\{(0,0)\}$ gives the fraction $1$ for both other
vertices, while its distance to the opposite edge is $1/\sqrt{2}$. The corrected statement below
sums the tight rows; it is exact in this example and implies the book's bound up to a factor
$\sqrt{|I|}$.

**Theorem 3.8, the first step.** Algorithm 3.3 starts the pairwise steps at a vertex $x_0$, but
specifies step sizes only for $t \ge 1$, and without a first Frank–Wolfe step with step size $1$
the primal gap $h_1$ is not bounded by $LD^2/2$. On $\operatorname{conv}\{e_1, e_2\}$ with
$f(x) = (\mu/2)\|x\|^2 + 10\mu x_1$, starting at $e_1$ with the step size $1/8$ that the formula of
Theorem 3.8 gives for $t = 0$ yields $h_1 \approx 8.64\mu > \mu = LD^2/2$. As in Garber and Meshi,
the formal run takes $x_1$ to be a Frank–Wolfe vertex for $f'(x_0)$.

**Theorem 3.8, the rate.** Following Garber and Meshi [@garber2016linear, Theorem 1], the book
states $f(x_t) - f(x^*) \le (LD^2/2)\exp(-\mu t/(8LD^2\|x^*\|_0))$. Their induction gives
$(LD^2/2)(1 - c)^{t-1}$ with $c = \mu/(16LD^2\|x^*\|_0)$, and the stated bound fails already for
$t = 1$: on $\operatorname{conv}\{e_1, e_2\}$ with $f(x) = (L/2)\|x - x^*\|^2$, $x^* = (0.99, 0.01)$
and $x_0 = e_1$, the Frank–Wolfe vertex is $x_1 = e_2$ and
$h_1 = 0.9801L > Le^{-1/32} \approx 0.9692L$. The formal statement uses the rate of the proof.
:::

Over a polytope, the Frank–Wolfe algorithm converges only at the rate $O(1/t)$ when the minimizer
lies on a face: the iterates zig-zag between vertices of that face, because the algorithm can only
move toward vertices and never away from them. Away steps [@guelat1986some] remove weight from a
vertex that is currently used, fully-corrective steps reoptimize over all vertices used so far, and
pairwise steps move weight directly from one vertex to another. With the pyramidal width of
@lacostejulien2015global as the measure of the polytope's geometry, all three variants converge
linearly for smooth strongly convex objectives. This entry formalizes Sections 2.2.4, 2.2.5 and
3.1.1 of the book *Conditional Gradient Methods* [@braun2025conditional], in the numbering of its
arXiv version, for a polytope $P = \operatorname{conv} V$ with $V$ a finite set in a
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

The proof follows the book: by induction on the number of vertices of $S$ in the minimal face of
$y$, pushing $x$ and $y$ away from a common vertex until either $y$ leaves the face of that vertex or
the vertex drops out of the representation of $x$. The reverse inequality holds as well.

```{prf:proposition} Pyramidal width as facial distance
:label: prop-away-step-frank-wolfe-facial-eq
:enumerator: 2.31

In a finite-dimensional real normed space, the pyramidal width of $\operatorname{conv} V$ equals
its facial distance.
```

For the upper bound, take a closest pair $y \in \operatorname{conv} F$,
$x \in \operatorname{conv}(V \setminus F)$, with $F$ the minimal face of $y$. A functional separating
the open $\delta$-neighbourhood of $\operatorname{conv} F$ from $\operatorname{conv}(V \setminus F)$ is
maximized at $y$ over $F$, hence constant on $F$ because $y$ lies in the relative interior of its
minimal face, and the scaling inequality at $(x, y)$ forces every scaling constant to be at most the
facial distance. The book states the proposition in Euclidean space; the proof works in every
finite-dimensional real normed space.

### Lower bounds from inequalities

If the polytope is given by inequalities $a_i \cdot x \le b_i$, every face is cut out by the rows
tight on it, and summing those rows gives a functional that separates the face from the other
vertices by their total slack.

```{prf:proposition} Pyramidal width from inequalities (corrected)
:label: prop-away-step-frank-wolfe-lower
:enumerator: 2.32

Let the inequalities $a_i \cdot x \le b_i$ hold on $V$, and let every vertex off a proper face be
slack in some row that is tight on the face. Then the pyramidal width is at least the minimum of
$\dfrac{\sum_{i \in I} (b_i - a_i \cdot v)}{\|\sum_{i \in I} a_i\|}$ over row sets $I$ tight at some
vertex and vertices $v$ with positive total slack on $I$.
```

For an inequality description of $\operatorname{conv} V$ the hypothesis holds. In Euclidean space
it implies the book's bound up to a factor: with $s = b_I - A_I v \ge 0$,
$\sum_i s_i \ge \|s\|_2$ and $\|\sum_{i \in I} a_i\| \le \sqrt{|I|}\,\|A_I\|$, so the pyramidal
width is at least the minimum of $\|b_I - A_I v\|_2 / (\sqrt{|I|}\,\|A_I\|)$.

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

## Pairwise Frank–Wolfe

The pairwise variant of Section 3.1.1 combines the two steps of away-step Frank–Wolfe: it moves
weight from the away vertex directly to the Frank–Wolfe vertex.

```{prf:definition} Pairwise Frank–Wolfe run
:label: def-away-step-frank-wolfe-pfw
:nonumber:

A run starts at a vertex with weight $1$. In each step, with a Frank–Wolfe vertex $v_t$ and an away
vertex $a_t$ of the active set, the weight $\gamma_t = \min\{f'(x_t)(a_t - v_t)/(L\|a_t - v_t\|^2),
\lambda_{a_t}\}$ moves from $a_t$ to $v_t$, so $x_{t+1} = x_t + \gamma_t (v_t - a_t)$, and $a_t$
leaves the active set when its weight is used up, as in Algorithm 3.1.
```

```{prf:theorem} Linear convergence of pairwise Frank–Wolfe
:label: thm-away-step-frank-wolfe-pairwise
:enumerator: 3.2

Under the assumptions of Theorem 2.29, every run satisfies
$f(x_t) - f(x^*) \le (1 - \min\{1/2, \mu\delta^2/(LD^2)\})^{\lfloor (t-1)/(2|V|! + 2) \rfloor}
LD^2/2$ for $t \ge 1$.
```

A step whose weight is not used up is a good step: by Lemma 2.27 it contracts the primal gap. A
step that uses up the weight of the away vertex is a drop step if the Frank–Wolfe vertex is already
active, and a swap step otherwise. Drop steps shrink the active set, so they cannot outnumber good
steps by more than one. A swap step moves the whole weight of one vertex to a new vertex: the
weights are permuted while $f$ strictly decreases, so no weight vector repeats, and fewer than
$|V|!$ swap steps can follow each other.

## Decomposition-invariant pairwise Frank–Wolfe

Away-step and pairwise Frank–Wolfe maintain an explicit convex decomposition of the iterate. The
decomposition-invariant variant of Garber and Meshi [@garber2016linear], in the form of Bashiri and
Zhang [@bashiri2017decomposition], instead takes the away vertex from the minimal face of the
iterate. On simplex-like polytopes this face is read off from the support of the iterate, and step
sizes that are powers of $1/2$ keep the iterates feasible.

```{prf:definition} Simplex-like polytope
:label: def-away-step-frank-wolfe-simplex-like
:nonumber:

A polytope $P = \operatorname{conv} V \subseteq \mathbb{R}^n$ is simplex-like if
$V \subseteq \{0, 1\}^n$ and $P = \{x \in \mathbb{R}^n \mid x \ge 0,\ Ax = b\}$.
```

```{prf:definition} Decomposition-invariant pairwise Frank–Wolfe run
:label: def-away-step-frank-wolfe-dipfw
:nonumber:

A run starts at some $x_0 \in P$, and $x_1$ is a Frank–Wolfe vertex for $f'(x_0)$. For $t \ge 1$,
$x_{t+1} = x_t + \gamma_t (v_t - a_t)$, where $v_t$ is a Frank–Wolfe vertex and $a_t$ maximizes
$f'(x_t)$ over the vertices whose support lies in that of $x_t$, as in Algorithm 3.3.
```

```{prf:lemma} Sparsity scaling
:label: lem-away-step-frank-wolfe-sparsity-scaling
:nonumber:

Let $P$ be simplex-like, $x, y \in P$, $\psi$ a direction, $a$ a vertex maximizing $\psi$ over the
vertices whose support lies in that of $x$, and $v$ a Frank–Wolfe vertex. Then
$\psi(x - y) \le \sqrt{\|y\|_0}\, \|x - y\|\, \psi(a - v)$, where $\|y\|_0$ is the number of
nonzero coordinates of $y$.
```

The proof follows Garber and Meshi [@garber2016linear, Lemma 2], with the decomposition of Garber
and Hazan [@garber2016linearly, Lemma 5.3]. Write $y = \sum_u \gamma_u u$ and, among all ways to
write $x = \sum_u (\gamma_u - \Delta_u) u + (\sum_u \Delta_u) z$ with $z \in P$, take one with
minimal $\sum_u \Delta_u$. Then every $u$ with $\Delta_u > 0$ has a coordinate $j$ with
$z_j = 0 < y_j$, since otherwise weight could move from $z$ back to $u$ without leaving $P$, and
Cauchy–Schwarz on these coordinates bounds $\sum_u \Delta_u$ by $\sqrt{\|y\|_0}\, \|x - y\|$.

```{prf:lemma} Feasibility of DI-PFW
:label: lem-away-step-frank-wolfe-dipfw-feasible
:nonumber:

If $P$ is simplex-like and the step sizes $\gamma_t$, $t \ge 1$, are nonincreasing powers of $1/2$,
every run stays in $P$.
```

The coordinates of $x_t$ are integer multiples of $\gamma_t$, and $a_t$ vanishes wherever $x_t$
does, so a coordinate that the step decreases is at least $\gamma_t$.

```{prf:theorem} Decomposition-invariant pairwise Frank–Wolfe
:label: thm-away-step-frank-wolfe-dipfw
:enumerator: 3.8

Let $P$ be simplex-like, let $f$ be $L$-smooth and $\mu$-strongly convex on $P$ with minimizer
$x^*$, and let $c = \mu/(16LD^2\|x^*\|_0)$. If the step sizes $\gamma_t$, $t \ge 1$, are
nonincreasing powers of $1/2$ in $[\eta_t/2, \eta_t]$ with $\eta_t = \sqrt{c}\,(1 - c)^{(t-1)/2}$,
every run satisfies $f(x_t) - f(x^*) \le (LD^2/2)(1 - c)^{t-1}$ for $t \ge 1$.
```

The step sizes of the book, the largest power of $1/2$ below $\eta_t$, satisfy these assumptions.
Sparsity scaling and strong convexity at $x_t$ give $\|x^*\|_0\, f'(x_t)(a_t - v_t)^2 \ge
2\mu h_t$, so as long as $h_t \le (LD^2/2)(1 - c)^{t-1}$ the step gains at least $4ch_t$, while the
quadratic term costs at most $c\,(LD^2/2)(1 - c)^{t-1}$. Here $c \le 1/16$, because two distinct
$0/1$ vertices give $D \ge 1$ and $\mu \le L$.

:::{note}
**Differences from the book.** The theorems are stated for any constant $\delta > 0$ with the
scaling property, in particular the pyramidal width. In Theorem 2.29 the contraction factor is
$1 - \min\{1/2, \mu\delta^2/(4LD^2)\}$; the book's $1 - \mu\delta^2/(4LD^2)$ is the same whenever
$\mu\delta^2 \le 2LD^2$, which its proof uses. The exponent is $\lfloor (t-1)/2 \rfloor$ instead of
the book's $\lceil (t-1)/2 \rceil$: after the first step the active set can contain two vertices, and
the formal count of drop steps allows one more drop step than good steps. In Theorem 3.2 the
exponent is $\lfloor (t-1)/(2|V|! + 2) \rfloor$; the book's $(t-1)/(3|V|! + 1)$ is never larger,
up to rounding down.
:::

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/AwayStepFW/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/away-step-frank-wolfe.md
```
