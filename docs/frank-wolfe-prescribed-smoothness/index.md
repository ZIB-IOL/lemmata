---
title: Frank–Wolfe oracle complexity with prescribed set smoothness
numbering:
  headings: false
---

```{include} ../_generated/provenance/frank-wolfe-prescribed-smoothness.md
```

:::{note}
A short note on arXiv is in preparation. This page contains the statements and the proofs; every
result is checked in Lean.
:::

Frank–Wolfe methods access the feasible region only through a *linear minimization oracle*
(LMO), which returns a minimizer of a linear function over the region. On strongly convex
regions, accuracy $\varepsilon$ requires on the order of $1/\sqrt\varepsilon$ oracle calls, and
this is optimal [@grimmer2026lower; @pokutta2026lower]. This entry answers the same question for
*smooth* regions, whose unit outer normals change in a Lipschitz way along the boundary.

Smoothness of the region does not improve the order $1/T$. A convex body whose unit normals are
$\beta$-Lipschitz is a smaller convex body $K$, of diameter $D - 2/\beta$, plus a ball of radius
$1/\beta$ ([](#lem-frank-wolfe-prescribed-smoothness-rolling)). Frank–Wolfe applied to $K$ reaches
primal gap $2L(D - 2/\beta)^2/(T + 1)$ after $T$ oracle calls for the quadratic
$\frac L2\|x - u\|^2$. No method does better than a constant fraction of this with probability
at least $1/5$, even when the quadratic is known, the method is randomized, and every linear
minimizer is unique.

| Methods | LMO | After at most $T$ oracle calls | |
|---|---|---|---|
| all | unique minimizers | infeasible output or primal gap $\ge L(D - 2/\beta)^2/(64(T+1))$, with probability $\ge 1/5$ | [](#thm-frank-wolfe-prescribed-smoothness-main) |
| feasible outputs | unique minimizers | primal gap $\ge L(D - 2/\beta)^2/(64(T+1))$, with probability $\ge 3/4$ | [](#thm-frank-wolfe-prescribed-smoothness-unique-feasible) |
| all | vertex LMO | infeasible output or primal gap $\ge L(D - 2/\beta)^2/(32(T+1))$, with probability $\ge 1/4$ | [](#thm-frank-wolfe-prescribed-smoothness-vertex) |
| deterministic | vertex LMO | the same, always, in dimension $64(T+1) + 1$ | [](#thm-frank-wolfe-prescribed-smoothness-deterministic) |
| Frank–Wolfe on the inner parallel body | any | primal gap $\le 2L(D - 2/\beta)^2/(T+1)$ for isotropic quadratics | [](#thm-frank-wolfe-prescribed-smoothness-upper) |

The bound for feasible outputs with the vertex LMO, the penalty for infeasible outputs, the
upper bound for general smooth objectives and the linear rate for bodies that are also strongly
convex are stated below.

## Setting

Throughout, $\langle\cdot,\cdot\rangle$ is a real inner product with norm $\|\cdot\|$, $B_r$ is
the closed ball of radius $r$ about the origin, and a *convex body* is a compact convex set with
nonempty interior.

```{prf:definition} Smooth sets
:label: def-frank-wolfe-prescribed-smoothness-smooth

A vector $n$ with $\|n\| = 1$ is a *unit outer normal* of a set $C$ at $z \in C$ if
$\langle n, y\rangle \le \langle n, z\rangle$ for every $y \in C$. The set $C$ is
*$\beta$-smooth* if

$$
\|n - m\| \le \beta\,\|z - w\|
$$

for all $z, w \in C$, every unit outer normal $n$ at $z$ and every unit outer normal $m$ at $w$.
```

Each boundary point of a $\beta$-smooth set has exactly one unit outer normal. A linear function
may still be minimized by a whole face.

```{prf:definition} Linear minimization oracle
:label: def-frank-wolfe-prescribed-smoothness-lmo

A *linear minimization oracle* (LMO) of a set $C$ is a map $O$ that answers every direction $q$
with a point $O(q) \in C$ satisfying $\langle q, O(q)\rangle \le \langle q, y\rangle$ for all
$y \in C$.
```

When several points minimize $\langle q, \cdot\rangle$, an LMO selects one of them; a fixed
selection is a *tie-breaking rule*. For $q = 0$ every point of $C$ is a minimizer.

```{prf:definition} Methods requiring no more than $T$ oracle calls
:label: def-frank-wolfe-prescribed-smoothness-method

A deterministic method requiring no more than $T$ oracle calls either returns a point, or calls
the LMO with a direction $q$ and continues, depending on the answer, as a method requiring no
more than $T - 1$ calls. Run against an LMO $O$, it returns a point, which need not be feasible.
A *randomized method* is a family of deterministic methods indexed by the outcome $\omega$ of a
random experiment, with an arbitrary probability law.
```

The objective is known to the method, so evaluating it or its gradient is not an oracle call.
In the lower bounds, the hard instance may depend on the method, but not on $\omega$.

```{prf:definition} Measurable methods
:label: def-frank-wolfe-prescribed-smoothness-measurable

A randomized method is *measurable* if, against every measurable LMO, its output is a measurable
function of $\omega$.
```

For example, a method whose directions and output are jointly measurable functions of $\omega$
and of the previous answers is measurable.

```{prf:definition} The objective of the lower bounds
:label: def-frank-wolfe-prescribed-smoothness-objective

Write the points of $\mathbb R^N \times \mathbb R$ as $(x, y)$ and let

$$
f(x, y) = \frac L2\left(\|x\|^2 + y^2\right) + \frac{32L}{\beta}\,y .
$$
```

Up to an additive constant, $f$ is $\frac L2\|\cdot - c\|^2$ with $c = (0, -32/\beta)$. It is
$L$-smooth and $L$-strongly convex, and the method knows it.

## The main result

In the main result every nonzero direction has exactly one minimizer, so the LMO has no choice
to make, and no tie-breaking rule can reveal anything.

```{prf:definition} The LMO of a body with unique minimizers
:label: def-frank-wolfe-prescribed-smoothness-unique-oracle

Let $C$ be a convex body on which $\langle q, \cdot\rangle$ has exactly one minimizer for every
$q \ne 0$, and let $x_0 \in C$. The LMO $O_{C, x_0}$ answers $q \ne 0$ with this minimizer and
$q = 0$ with $x_0$.
```

```{prf:definition} The class of bodies
:label: def-frank-wolfe-prescribed-smoothness-class

For $\beta, D > 0$ and a point $x_0$, the class $\mathcal C(\beta, D, x_0)$ consists of the
$\beta$-smooth convex bodies $C$ with $\operatorname{diam} C \le D$ and $x_0 \in C$ on which
$\langle q, \cdot\rangle$ has exactly one minimizer for every $q \ne 0$.
```

```{prf:theorem} Lower bound without tie-breaking
:label: thm-frank-wolfe-prescribed-smoothness-main

Let $T \ge 0$, $L, \beta > 0$ and $\beta D > 2$. Put $N = 256(T+1)$ and $x_0 = (a_0 e_1, 0)$ in
$\mathbb R^N \times \mathbb R$, where $a_0 = 0.99\,(D - 2/\beta)/\sqrt 2$. For every measurable
randomized method requiring no more than $T$ oracle calls there is a body $C$ in
$\mathcal C(\beta, D, x_0)$, depending on the method but not on $\omega$, such that, run against
$O_{C, x_0}$, the method returns with probability at least $1/5$ a point $w$ with

$$
w \notin C \quad\text{or}\quad f(w) - \min_C f \;\ge\; \frac{L(D - 2/\beta)^2}{64(T+1)} .
$$
```

```{prf:theorem} Methods with feasible outputs
:label: thm-frank-wolfe-prescribed-smoothness-unique-feasible

In the setting of [](#thm-frank-wolfe-prescribed-smoothness-main), suppose the method returns a
point of $C$ when run against $O_{C, x_0}$, for every body $C$ in $\mathcal C(\beta, D, x_0)$ and
every $\omega$. Then some body $C$ in $\mathcal C(\beta, D, x_0)$, depending on the method but
not on $\omega$, gives

$$
f(w) - \min_C f \;\ge\; \frac{L(D - 2/\beta)^2}{64(T+1)}
$$

with probability at least $3/4$, and expected primal gap at least
$3L(D - 2/\beta)^2/(256(T+1))$.
```

The dimension $N + 1$ grows linearly with $T$, so the bounds concern the worst case over all
dimensions. Returning an infeasible point counts as a failure. Frank–Wolfe methods return convex
combinations of oracle answers, which are feasible, and for them the probability is $3/4$. The
proofs are given [after the lower bounds for the vertex LMO](#sec-frank-wolfe-prescribed-smoothness-proof),
on which they build.

## The hard bodies

The bodies of the lower bounds are rounded simplices. An instance is an index set $I$, which
determines the vertices of the simplex; the objective is the same for all instances.

```{prf:definition} The hard bodies
:label: def-frank-wolfe-prescribed-smoothness-family

Let $r = 1/\beta$ and $a = (D - 2/\beta)/\sqrt 2$. For an index set
$I \subseteq \{1, \dots, N\}$, let $\Delta_I$ be the set of weight vectors $u \in \mathbb R^N$
with $u \ge 0$, $u_i = 0$ for $i \notin I$ and $\sum_{i \in I} u_i = 1$. The *lifted simplex*
$S_I = \{(a u, r) : u \in \Delta_I\}$ is the scaled simplex on $I$ at height $r$, and the hard
body is the lifted simplex rounded by the ball of radius $r$:

$$
C_I = S_I + B_r .
$$
```

```{prf:definition} The vertex LMO
:label: def-frank-wolfe-prescribed-smoothness-vertex-oracle

For $q = (q_x, q_y) \ne 0$, let $j$ be the index in $I$ with the smallest coordinate $q_{x,j}$,
and the smallest such index if several coordinates are equal. The *vertex LMO* of $C_I$ answers
$q$ with $(a e_j, r) - r\,q/\|q\|$, and $q = 0$ with $(a e_1, 0)$.
```

The vertex LMO minimizes $\langle q, \cdot\rangle$ over each of the two summands of $C_I$
separately, so it is an LMO of $C_I$ when $1 \in I$.

```{prf:proposition} Properties of the hard bodies
:label: prop-frank-wolfe-prescribed-smoothness-family

Let $1 \in I$ and $|I| \ge 2$. Then $C_I$ is a convex body of diameter exactly $D$. It is
$\beta$-smooth, and not $\beta'$-smooth for any $\beta' < \beta$. It is not strongly convex: for
no $\alpha > 0$ is it $(\alpha, 2)$-uniformly convex. The vertex LMO is an LMO of $C_I$.
```

```{prf:proof} of [](#prop-frank-wolfe-prescribed-smoothness-family)
:nonumber:

*Smoothness.* Write a point of $C_I$ as $z = s + b$ with $s \in S_I$ and $\|b\| \le r$. If $n$ is
a unit outer normal at $z$, comparing $z$ with $s + rn$ gives $b = rn$, and $s$ maximizes
$\langle n, \cdot\rangle$ on $S_I$. For a second point $w = s' + rm$ this gives
$\langle n - m, s - s'\rangle \ge 0$, hence
$r\|n - m\|^2 \le \langle n - m, z - w\rangle \le \|n - m\|\,\|z - w\|$. The points directly
above and below a point of $S_I$ are $2r$ apart and have opposite normals, so no constant below
$1/r = \beta$ works.

*Diameter.* The simplex has diameter $\sqrt 2\,a$, attained at two vertices. Extending that
segment by $r$ at both ends gives two points of $C_I$ at distance $2r + \sqrt 2\,a = D$.

*No strong convexity.* Two bottom points $(a e_i, 0)$ and $(a e_j, 0)$ have their midpoint at
height $0$, the lowest height in $C_I$, so no ball around the midpoint lies in $C_I$.
```

Where does $f$ attain its minimum on $C_I$?

```{prf:proposition} The minimizer of the objective
:label: prop-frank-wolfe-prescribed-smoothness-optimum

Let $|I| \ge 2$, $c = (0, -32r)$, let $o = (a\mathbf 1_I/|I|, r)$ be the center of $S_I$, and
$H = \|o - c\|$. The point $z^\star = o + (r/H)(c - o)$ minimizes $f$ on $C_I$.
For the vertex LMO, local dual sharpness in the sense of @pokutta2026frank
(see [Frank–Wolfe beyond 1/t under local dual sharpness](../frank-wolfe-local-dual-sharpness/index.md))
fails at $z^\star$: for every set $M$ containing $z^\star$, every $A > 0$ and every exponent
$q$, $C_I$ with the vertex LMO is not locally dually sharp around $M$ with constants $(A, q)$.
```

```{prf:proof} of [](#prop-frank-wolfe-prescribed-smoothness-optimum)
:nonumber:

Up to a constant, $f = \frac L2\|\cdot - c\|^2$. Every point $v \in S_I$ satisfies
$\langle v - o, o - c\rangle = 0$, because $o - c = (a\mathbf 1_I/|I|, 33r)$ and the weights of
$v$ sum to one. For $z = v + b \in C_I$ with $\|b\| \le r$ this gives
$H\|z - c\| \ge \langle z - c, o - c\rangle \ge H^2 - rH$, so
$\|z - c\| \ge H - r = \|z^\star - c\|$. In the direction $g = o - c$, which is parallel to
$\nabla f(z^\star)$, all coordinates $g_{x,i}$ with $i \in I$ are equal. The vertex LMO answers
$s = (a e_j, r) - r g/H$ for a single index $j$, and then $z^\star - s = o - (a e_j, r) \ne 0$
while $\langle g, z^\star - s\rangle = 0$.
```

So the hard bodies lie outside the regime in which Frank–Wolfe converges faster than $1/t$, as
they must. The tie-breaking rule matters for another reason. In the vertical direction
$q = (0, 1)$ every point of the bottom face $\{(a u, 0) : u \in \Delta_I\}$ is a minimizer, and
an LMO that answered with the barycenter $(a\mathbf 1_I/|I|, 0)$ of that face would reveal $I$
in a single call. The main result excludes such answers by making every minimizer unique.

## Lower bounds with the vertex LMO

The vertex LMO reveals little per call. A query $q \ne 0$ orders the indices by their
coordinates $q_{x,j}$. The answer reveals the first index of $I$ in this order, and with it that
the indices before it do not lie in $I$; nothing else about $I$ can be read off. Index $1$
belongs to every instance, so the answer $(a e_1, 0)$ to $q = 0$ lies in every $C_I$ and reveals
nothing. After $T$ calls a method thus knows at most $T + 1$ indices of $I$, but a point with
small primal gap must put most of its horizontal weight on $I$.

```{prf:theorem} Lower bound with the vertex LMO
:label: thm-frank-wolfe-prescribed-smoothness-vertex

Let $T \ge 0$, $L, \beta > 0$, $\beta D > 2$ and $N = 256(T+1)$. For every measurable randomized
method requiring no more than $T$ calls to the vertex LMO there is an index set $I$ with
$|I| = 8(T+1)$ and $1 \in I$, depending on the method but not on $\omega$, such that the method
returns with probability at least $1/4$ a point $w$ with

$$
w \notin C_I \quad\text{or}\quad f(w) - \min_{C_I} f \;\ge\; \frac{L(D - 2/\beta)^2}{32(T+1)} .
$$
```

By [](#prop-frank-wolfe-prescribed-smoothness-family), the body $C_I$ has diameter exactly $D$
and is $\beta$-smooth. The proof uses that the answers determine the instance only up to the
indices not yet decided. Fix a deterministic method, and let $I$ be uniformly distributed over
the index sets of size $d = 8(T+1)$ that contain $1$. After some answers, let $P$ be the indices
known to lie in $I$ and $U$ the indices whose membership is still undecided, and put
$h = d - |P|$. Given these answers, $I$ is uniformly distributed over the sets $P \cup S$ with
$S \subseteq U$ and $|S| = h$, so an undecided index lies in $I$ with probability $h/|U|$.

```{prf:lemma} The expected ratio of undecided indices
:label: lem-frank-wolfe-prescribed-smoothness-posterior

For a deterministic method requiring no more than $T$ calls to the vertex LMO, and $I$ uniformly
distributed as above, the ratio $h/|U|$ at the end of the run satisfies

$$
\mathbb E\left[\frac{h}{|U|}\right] = \frac{d - 1}{N - 1} = \frac{8(T+1) - 1}{256(T+1) - 1} .
$$
```

```{prf:proof} of [](#lem-frank-wolfe-prescribed-smoothness-posterior)
:nonumber:

Two instances give the same answers exactly when they agree on all decided indices, and all
instances have the same probability; this gives the uniform distribution over the sets
$P \cup S$. Each answer decides the indices of $U$ that come before the first index of $I$ in
the order of the query, one by one. When the next index is decided, it lies in $I$ with
probability $h/|U|$, and the ratio becomes $(h - 1)/(|U| - 1)$; otherwise it becomes
$h/(|U| - 1)$. The weighted mean of the two is $h/|U|$, so the expected ratio never changes, and
it is $(d - 1)/(N - 1)$ at the start, where $P = \{1\}$. The formal proof writes this as a
counting identity: over the $\binom{|U|}{h}$ consistent instances the ratios sum to
$\binom{|U| - 1}{h - 1}$, and both binomial coefficients split by Pascal's rule at each decided
index.
```

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-vertex)
:nonumber:

Write $k = T + 1$, so that $|I| = d = 8k$ and $N = 256k$. The barycenter $(a\mathbf 1_I/d, 0)$
of the bottom face gives $\min_{C_I} f \le La^2/(16k)$.

*Step 1: a point with little weight on $I$ fails.* For a point $w = (x, y)$, let
$w_i = |x_i|/a$ if $\|x\|^2 \le a^2/(4k)$, and $w_i = 0$ otherwise; then
$k\sum_i w_i^2 \le 1/4$. Suppose that $\sum_{i \in I} w_i \le 3/4$ and $w \in C_I$; we show
$f(w) \ge La^2/(8k)$. If $\|x\|^2 > a^2/(4k)$, then $f(w) \ge \frac L2\|x\|^2$ gives this
directly. Otherwise some $u \in \Delta_I$ satisfies $\|x - a u\|^2 + (y - r)^2 \le r^2$, so
$\|x - a u\|^2 \le 2ry$. Since $\sum_{i \in I} x_i \le 3a/4$, we have
$\sum_{i \in I}(a u_i - x_i) \ge a/4$, and Cauchy–Schwarz gives
$a^2/16 \le d\,\|x - a u\|^2 \le 2 d r y$. Hence $f(w) \ge 32 L r y \ge La^2/(8k)$. In both cases
$f(w) - \min_{C_I} f \ge La^2/(16k)$.

*Step 2: little weight on $I$ is likely.* Fix $\omega$, so that the method is deterministic, and
let $I$ be uniformly distributed as above. The output depends only on the answers. Given the
final answers, index $i$ lies in $I$ with probability $p_i$, where $p_i = 1$ for $i \in P$,
$p_i = h/|U|$ for $i \in U$, and $p_i = 0$ otherwise. By the inequality
$p_i w_i \le p_i^2/(4k) + k w_i^2$, the expected weight on $I$ is at most

$$
\frac{\mathbb E\left[|P| + h \cdot h/|U|\right]}{4k} + k\sum_i w_i^2
\;\le\; \frac{k + d\,\mathbb E[h/|U|]}{4k} + \frac14 \;\le\; \frac{5}{16} + \frac14 = \frac9{16},
$$

using $|P| \le k$ and [](#lem-frank-wolfe-prescribed-smoothness-posterior). By Markov's
inequality the weight on $I$ is at most $3/4$ with probability at least $1/4$, and by Step 1 the
method then fails.

*Step 3: one instance for all outcomes $\omega$.* Averaging Step 2 over $\omega$ shows that the
probability of failure, averaged over the index sets $I$, is at least $1/4$; some $I$ attains at
least the average. Finally, $La^2/(16k) = L(D - 2/\beta)^2/(32(T+1))$.
```

```{prf:corollary} Vertex LMO, methods with feasible outputs
:label: cor-frank-wolfe-prescribed-smoothness-feasible

Suppose that, for every index set $I$ containing $1$ and every $\omega$, the method returns a
point of $C_I$ when run against the vertex LMO of $C_I$. Then some index set $I$ with
$|I| = 8(T+1)$ and $1 \in I$, depending on the method but not on $\omega$, gives

$$
f(w) - \min_{C_I} f \;\ge\; \frac{L(D - 2/\beta)^2}{32(T+1)}
$$

with probability at least $3/4$, and expected primal gap at least
$3L(D - 2/\beta)^2/(128(T+1))$.
```

```{prf:proof} of [](#cor-frank-wolfe-prescribed-smoothness-feasible)
:nonumber:

Fix $\omega$ and let $I$ be uniformly distributed as in
[](#lem-frank-wolfe-prescribed-smoothness-posterior).

*One instance with little weight suffices.* All instances consistent with the final answers
give the same output $w$, and $w$ lies in the body of each of them. If one of them, $J$, has
$\sum_{i \in J} w_i \le 3/4$, Step 1 of the previous proof, applied to $J$, gives
$f(w) \ge La^2/(8k)$, and then $f(w) - \min_{C_I} f \ge La^2/(16k)$ for every consistent $I$.

*Many undecided indices leave such an instance.* If $|U| \ge 127k$ at the end, the membership
probabilities satisfy $\sum_i p_i^2 = |P| + h^2/|U| \le k + 64k/127 < 9k/4$. The inequality
$p_i w_i \le p_i^2/(6k) + \frac{3k}{2} w_i^2$ then shows that the consistent instances have
average weight at most $3/4$, so one of them has weight at most $3/4$.

*Few indices are found not to lie in $I$.* Each decided index either lies in $I$, which happens
at most $k$ times, or is found not to lie in $I$. So if at most $128k$ indices are found not to
lie in $I$, then $|U| \ge 127k$ at the end. Let $X$ be the number of these indices. Summed over
the $\binom{|U|}{h}$ consistent instances, a run with $t$ calls left finds at most
$t\binom{|U|}{h + 1}$ of them: at each decided index both binomial coefficients split by
Pascal's rule, an index found outside $I$ adds one to $X$ without using a call, and an index
found in $I$ ends the call. At the start this is $31T$ per instance, so by Markov's inequality
$X > 128k$ has probability at most $31T/(128k) < 31/128$. The method therefore fails with
probability at least $97/128 \ge 3/4$.

*Averaging.* Averaging over $\omega$ selects one index set $I$ as before. The primal gap of a
feasible point is nonnegative and bounded on $C_I$, which gives the expectation.
```

The note's Appendix A gives the probability $5/7$ here; counting the excluded indices exactly
improves it to $97/128$.

```{prf:theorem} Deterministic methods
:label: thm-frank-wolfe-prescribed-smoothness-deterministic

Let $N = 64(T+1)$. For every deterministic method requiring no more than $T$ calls to the vertex
LMO there is an index set $I$ with $|I| = 8(T+1)$ and $1 \in I$ such that $C_I$ has diameter $D$
and the method returns a point $w$ with

$$
w \notin C_I \quad\text{or}\quad f(w) - \min_{C_I} f \;\ge\; \frac{L(D - 2/\beta)^2}{32(T+1)} .
$$
```

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-deterministic)
:nonumber:

Answer every query $q \ne 0$ as if the first index in its order belonged to $I$, and record that
index. Let $P$ be the recorded indices together with index $1$; then $|P| \le k = T + 1$, and
every index set containing $P$ produces exactly these answers and hence the same output $w$.
Now complete $P$ to an index set $I$ of size $8k$ by indices chosen uniformly among the remaining
$N - |P| \ge 63k$. The membership probabilities satisfy
$\sum_i p_i^2 \le k + 64k/63 < 9k/4$, so, as in the proof of
[](#cor-frank-wolfe-prescribed-smoothness-feasible), some such $I$ has
$\sum_{i \in I} w_i \le 3/4$, and the method fails on it by Step 1 of the proof of
[](#thm-frank-wolfe-prescribed-smoothness-vertex). For a randomized method the recorded indices
depend on $\omega$, which is why the randomized bounds need the larger dimension.
```

Methods that may return infeasible points can also be measured by a penalty on the distance to
the feasible region, as proposed by @grimmer2026lower.

```{prf:definition} Penalized error
:label: def-frank-wolfe-prescribed-smoothness-penalized

For a weight $\rho > 0$, the *penalized error* of a point $w$ for $C_I$ is

$$
E_I(w) = f(w) - \min_{C_I} f + \rho\,\operatorname{dist}(w, C_I) .
$$
```

```{prf:theorem} A penalty for infeasible outputs
:label: thm-frank-wolfe-prescribed-smoothness-penalty

In the setting of [](#thm-frank-wolfe-prescribed-smoothness-vertex), let
$\rho \ge L(2D + 32/\beta)$, and assume nothing about feasibility. Some index set $I$ with
$|I| = 8(T+1)$ and $1 \in I$, depending on the method but not on $\omega$, gives

$$
E_I(w) \;\ge\; \frac{L(D - 2/\beta)^2}{256(T+1)}
$$

with probability at least $1/4$, and $\mathbb E\,E_I(w) \ge L(D - 2/\beta)^2/(1024(T+1))$; the
expectation may be infinite.
```

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-penalty)
:nonumber:

Let $v$ be the point of $C_I$ nearest to $w$, and $\delta = \|w - v\|$. On $C_I$ the gradient
of $f$ has norm at most $L(a + 34r)$, so $f(w) \ge f(v) - L(a + 34r)\delta$. The weight
$\rho \ge L(2D + 32/\beta)$ is at least $L(2a + 34r)$, hence
$E_I(w) \ge f(v) - \min_{C_I} f + La\delta$.

After rescaling we may assume $a = L = 1$; the threshold then reads $1/(128k)$. Consider the
event that the weight of $w$ on $I$ is at most $3/4$, which has probability at least $1/4$ by
Step 2 of the proof of [](#thm-frank-wolfe-prescribed-smoothness-vertex). If
$\delta \ge 1/(128k)$, then $E_I(w) \ge \delta$ suffices. Otherwise $v$ is close to $w$. If
$\|x\|^2 > 1/(4k)$, where $x$ is the horizontal part of $w$, the horizontal part of $v$ has
squared norm at least $9/(64k)$, and $f(v) \ge 9/(128k)$. If not, the horizontal coordinates of
$v$ on $I$ sum to at most $3/4 + \sqrt{8k}\,\delta \le 4/5$, and the argument of Step 1 gives
$f(v) \ge 2/(25k)$. Subtracting $\min_{C_I} f \le 1/(16k)$ leaves at least $1/(128k)$ in both
cases. Averaging over $\omega$ selects one index set, and Markov's inequality gives the
expectation.
```

(sec-frank-wolfe-prescribed-smoothness-proof)=
## Proof of the main result

The vertex LMO breaks ties by index. To dispense with any tie-breaking rule, every nonzero
direction must have a unique minimizer. Thickening the simplex symmetrically achieves this, but
it reveals $I$.

```{prf:proposition} A symmetric thickening reveals the index set
:label: prop-frank-wolfe-prescribed-smoothness-symmetric

Let $A, s > 0$ and let $K$ be the union of the balls of radius $s(1 - \|u\|^2)$ about the points
$\sum_{j \in I} u_j (A e_j, 1)$, $u \in \Delta_I$. Every lowest point of $K + B_1$ has
horizontal coordinates $A/|I|$ on $I$ and $0$ elsewhere, so a single call in the vertical
direction reveals $I$.
```

```{prf:proof} of [](#prop-frank-wolfe-prescribed-smoothness-symmetric)
:nonumber:

All the points $(A e_j, 1)$ have height $1$, so the lowest point of the ball about
$\sum_j u_j (A e_j, 1)$ has height $1 - s(1 - \|u\|^2)$. Minimizing the height over
$u \in \Delta_I$ means minimizing $\|u\|^2$, and by Cauchy–Schwarz the unique minimizer is the
uniform weight $u = \mathbf 1_I/|I|$.
```

So the vertices must also be perturbed: then the best vertex in a direction is unique and
reveals one index, just as with the vertex LMO.

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-main)
:nonumber:

Write $k = T + 1$ and $r = 1/\beta$. It suffices to construct bodies with rounding radius $1$,
simplex scale $A = 0.99(\beta D - 2)/\sqrt 2$ and threshold $(\beta D - 2)^2/(64k)$ for $L = 1$:
scaling by $r$ multiplies distances by $r$, turns $1$-Lipschitz normals into $\beta$-Lipschitz
ones, and multiplies primal gaps by $Lr^2$.

*The bodies.* An instance consists of an index set $I \ni 1$ with $|I| = 8k$ and a perturbation
$p_j$ of each vertex: $p_1 = 0$, and every coordinate of every other $p_j$ takes one of $Q$
equally spaced values, chosen uniformly and independently, with
$\|p_j\| \le \eta = A^2/(10^6 k (A + 36)^2)$. With the vertices $v_j = (A e_j, 1) + p_j$ and a
small $s > 0$, let $K$ be the union of the balls of radius $s(1 - \|u\|^2)$ about the points
$\sum_{j \in I} u_j v_j$, $u \in \Delta_I$; the body is $K + B_1$. Minimizing
$\langle q, \cdot\rangle$ over it amounts to minimizing
$\langle q, \sum_j u_j v_j\rangle + s\|u\|^2$ over $\Delta_I$, a strictly convex problem. So every
nonzero direction has exactly one minimizer, the body is $1$-smooth, and it contains
$x_0 = (A e_1, 0)$.

*Each answer reveals one index.* If an index $j \in I$ scores $\langle q, v_j\rangle$ more than
$2s$ above the best index of $I$, the minimizing weights vanish at $j$. As long as no index of
$I$ scores within $2s$ of the best one, the answer therefore depends on $I$ only through the best
index, that is, the first index of $I$ in the order of the scores. Steps 1 and 2 of the proof of
[](#thm-frank-wolfe-prescribed-smoothness-vertex) apply to every method that learns, with each
call, the first index of $I$ in an order of its choice. So, for every $\omega$, at least a
quarter of the index sets make the method fail on the unperturbed bodies, at threshold
$A^2/(16k)$, when the outputs are moved into the unperturbed bodies as below.

*Ambiguous answers are rare.* Given the previous answers, the next query is fixed, and it
depends only on the perturbations of the indices revealed so far. A competing index has a
coordinate in which the unit vector of the query is at least $1/\sqrt N$ in absolute value, and
one grid step in that coordinate changes its score by more than $4s$; so at most one value of
that coordinate brings it within $2s$ of the best index. Summing over the possible sequences of
answers, pairs of indices and coordinates, the perturbations for which some answer is ambiguous
have probability at most $1/100$, for every $\omega$.

*From the unperturbed to the perturbed bodies.* The two bodies are within distance $h = 2\eta$
of each other. The map $w \mapsto (w + h c_0)/(1 + h)$, with $c_0 = (A e_1, 1)$, moves every
point of the perturbed body into the unperturbed one, by at most $h(2A + 4)$, and $f$ is
$(A + 35)$-Lipschitz near both bodies. A primal gap of at least $A^2/(16k)$ of the moved point on
the unperturbed body thus leaves a primal gap of at least
$A^2/(16k) - (A + 35)(2A + 5)h \ge (\beta D - 2)^2/(64k)$ of the original point on the perturbed
body.

*Averaging.* For every $\omega$, at least a fraction
$\frac14\left(1 - \frac1{100}\right) \ge \frac15$ of the instances make the method fail.
Averaging over $\omega$ and taking the best instance gives one body with probability of failure
at least $1/5$. Its diameter is at most
$2 + \sqrt 2 A + 2h \le \beta D$, which becomes $D$ after scaling by $r$, and the threshold
becomes $L r^2 (\beta D - 2)^2/(64k) = L(D - 2/\beta)^2/(64(T+1))$.
```

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-unique-feasible)
:nonumber:

The perturbed bodies belong to the class, so the method returns points of them, and the map of
the previous proof moves these points into the unperturbed bodies. The method on the
unperturbed bodies that the proof compares with therefore returns feasible points, and the
argument of
[](#cor-frank-wolfe-prescribed-smoothness-feasible) makes at least a fraction $97/128$ of the
index sets fail, instead of $1/4$. The rest of the proof is unchanged, and
$\frac{97}{128} \cdot \frac{99}{100} \ge \frac34$. The primal gap is nonnegative and bounded on
the body, which gives the expectation.
```

## Upper bounds

```{prf:lemma} Inner balls and the inner parallel body
:label: lem-frank-wolfe-prescribed-smoothness-rolling

Let $C$ be a nonempty compact convex $\beta$-smooth set and $r = 1/\beta$. For every unit outer
normal $n$ of $C$ at $z \in C$, the ball $z - rn + B_r$ lies in $C$. Consequently $C = K + B_r$
for the *inner parallel body* $K = \{x : x + B_r \subseteq C\}$, and
$\operatorname{diam} C = \operatorname{diam} K + 2r$.
```

```{prf:proof} of [](#lem-frank-wolfe-prescribed-smoothness-rolling)
:nonumber:

Suppose the ball $z - rn + B_r$ is not contained in $C$. Take a point $p$ of the ball farthest
from $C$, at distance $\delta > 0$, and its nearest point $y \in C$; then $m = (p - y)/\delta$
is a unit outer normal at $y$. The point $p$ maximizes $\langle m, \cdot\rangle$ on the ball, so
$p = z - rn + rm$, and
$r^2\|m - n\|^2 = \|y - z\|^2 + 2\delta\langle m, y - z\rangle + \delta^2 > \|y - z\|^2$, which
contradicts smoothness. The set $K$ is compact and convex, every boundary point of $C$ lies in
$K + B_r$, and a separation argument gives $C = K + B_r$. Extending a diametral segment of $K$
by $r$ at both ends gives the diameter.
```

An LMO of $C$ yields one of $K$: if $s$ minimizes $\langle q, \cdot\rangle$ on $C$ and
$q \ne 0$, then $s + r q/\|q\|$ minimizes it on $K$. So Frank–Wolfe can run on $K$, using the
LMO of $C$.

```{prf:definition} Frank–Wolfe on the inner parallel body
:label: def-frank-wolfe-prescribed-smoothness-quadratic-method

For $f(x) = \frac L2\|x - u\|^2$ with $u$ known, call the LMO once with a fixed direction
$e \ne 0$ to obtain a point $a_0$ of $K$. Then perform $T - 1$ Frank–Wolfe steps on $K$, with
step sizes $2/(j + 2)$ and one LMO call per step, for the function
$F(a) = \min_{b \in B_r} f(a + b)$. Return $a + b$, where $a$ is the last iterate and $b$ is the
point of $B_r$ closest to $u - a$.
```

```{prf:theorem} Upper bound for isotropic quadratics
:label: thm-frank-wolfe-prescribed-smoothness-upper

Let $T \ge 2$ and $f(x) = \frac L2\|x - u\|^2$. Frank–Wolfe on the inner parallel body requires
no more than $T$ oracle calls and no gradient evaluation. For every compact convex
$\beta$-smooth set $C$ with $\operatorname{diam} C \ge 2/\beta$ and every LMO of $C$, it returns
a point $w \in C$ with

$$
f(w) - \min_C f \;\le\; \frac{2L(\operatorname{diam} C - 2/\beta)^2}{T + 1} .
$$
```

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-upper)
:nonumber:

The function $F$ has the gradient $\nabla f(a + b_a)$, where $b_a$ minimizes $f(a + \cdot)$ on
$B_r$, and it satisfies the affine lower bound and the quadratic upper bound of $f$ on $K$,
whose diameter is $\delta = \operatorname{diam} C - 2r$. The usual Frank–Wolfe recursion
$h_{j+1} \le (1 - \gamma_j) h_j + L\delta^2\gamma_j^2/2$ for the primal gaps $h_j$, with a full
first step, gives $h_j \le 2L\delta^2/(j + 2)$. The first call and $T - 1$ steps give the bound.
```

The objective of the lower bounds is of this form. Up to the constant factor and the
probability in [](#thm-frank-wolfe-prescribed-smoothness-main), Frank–Wolfe on the inner parallel
body is therefore optimal on $\beta$-smooth bodies of diameter at most $D$.

For a general smooth convex objective, conditional gradient sliding [@lan2016conditional]
applies to the product $K \times B_r$.

```{prf:definition} Conditional gradient sliding on $K \times B_r$
:label: def-frank-wolfe-prescribed-smoothness-sliding

Apply conditional gradient sliding, with the parameters of @lan2016conditional, to
$g(a, b) = f(a + b)$ on $K \times B_r$. Each outer iteration evaluates one gradient. It solves
the subproblem on $K$ approximately, by Frank–Wolfe steps with exact line search until the
Frank–Wolfe gap is small enough, and the subproblem on $B_r$ exactly.
```

```{prf:theorem} Smooth convex objectives
:label: thm-frank-wolfe-prescribed-smoothness-sliding

Let $f$ be differentiable and convex with $L$-Lipschitz gradient, and $C$ compact, convex and
$\beta$-smooth with $\operatorname{diam} C \ge 2/\beta$. Put
$\delta = \operatorname{diam} C - 2/\beta$ and $A = \delta^2 + 4/\beta^2$. For $n \ge 1$,
conditional gradient sliding on $K \times B_r$ evaluates exactly $n$ gradients, requires no more
than $1 + n + 9\delta^2 n(n + 1)/A$ oracle calls, and returns a point of $C$ with primal gap at
most $15LA/((n + 1)(n + 2))$.
```

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-sliding)
:nonumber:

The function $g$ is $2L$-smooth. With $\gamma_j = 3/(j + 2)$, $\tau_j = 6L/(j + 1)$ and
tolerances $\eta_j = 2LA/(j(j + 1))$, the three-point inequality gives
$h_j \le (1 - \gamma_j)h_{j-1} + \gamma_j\eta_j + \tfrac{\gamma_j\tau_j}2(d_{j-1} - d_j)$, which
telescopes with the weights $j(j + 1)(j + 2)$. A subproblem on $K$ with $H = \tau\delta^2$
requires no more than $1 + 6H/\eta$ oracle calls: one answer certifies it when $H \le \eta$;
otherwise exact line search reaches accuracy $\eta$ within $\lceil 2H/\eta\rceil$ steps, and
after that each step that does not yet certify lowers the objective by $\eta^2/(2H)$.
```

If the body is also strongly convex, in the sense of an outer ball at every boundary point, a
linear rate holds with one oracle call per iteration.

```{prf:definition} Projected gradient with Frank–Wolfe projections
:label: def-frank-wolfe-prescribed-smoothness-joint

Keep a point $a$ of the inner parallel body $K$ and an iterate $x \in a + B_r$. In each
iteration, take the gradient step $u = x - \nabla f(x)/L$. Unless $u$ is within distance $r$ of
$a$, call the LMO with the direction $a - u$ and move $a$ toward the resulting point of $K$ by
exact line search for $\frac12\|\cdot - u\|^2$. Then let $x$ be the point of $a + B_r$ closest to
$u$.
```

```{prf:theorem} A linear rate with inner and outer tangent balls
:label: thm-frank-wolfe-prescribed-smoothness-linear

Let $C$ be compact and convex, and suppose that every boundary point $s$ of $C$ with unit outer
normal $n$ satisfies $s - rn + B_r \subseteq C \subseteq s - Rn + B_R$, where $0 < r \le R$. Let
$f$ be $\mu$-strongly convex with $L$-Lipschitz gradient, and put
$c = \frac12\min\{1, r/(2(R - r))\}$ if $R > r$ and $c = 1$ if $R = r$. Started at any point of
$C$, projected gradient with Frank–Wolfe projections uses, in $n$ iterations, at most $n + 1$
gradients and at most $n + 1$ oracle calls, and returns a point $x_n \in C$ with

$$
f(x_n) - \min_C f \;\le\; \left(1 - c\,\frac{\mu}{L}\right)^n \frac{L(\operatorname{diam} C)^2}{2}.
$$

If $C$ is a ball ($R = r$), a variant with the same guarantee uses one oracle call in total.
```

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-linear)
:nonumber:

At the point of $K$ that the LMO returns, the outer ball gives $2(R - r)G \ge \|q\|\,\|s - a\|^2$
for the Frank–Wolfe gap $G$ of $\frac12\|\cdot - u\|^2$, so the line search reduces this
function by the factor $1 - c$ relative to any point of $K$. The function
$t \mapsto \tfrac12(\max\{0, \sqrt{2t} - r\})^2$ is convex and nondecreasing, and it turns this
into $Q(x') \le (1 - c)Q(x) + cQ(z)$ for every $z \in C$, where $Q = \tfrac12\|\cdot - u\|^2$.
Strong convexity at $x$ and the quadratic upper bound at $x'$ then give
$f(x') - f(w) \le (1 - c\mu/L)(f(x) - f(w))$ for every $w \in C$, and the first step starts at
primal gap at most $L(\operatorname{diam} C)^2/2$.
```

## Comparison with earlier bounds

```{prf:proposition} The bound of Grimmer and Liu at fixed parameters
:label: prop-frank-wolfe-prescribed-smoothness-comparison

For $d > T > 0$, $\delta \ge 0$ and $\beta > 0$, the quantity

$$
A_d = \frac{\delta}{2\sqrt d}\sqrt{1 - T/d} - \frac{1 - \sqrt{1 - T/d}}{\sqrt 2\,\beta}
$$

from the dimension-dependent lower bound of @grimmer2026lower for smooth sets satisfies
$A_d \le \beta\delta^2/(4\sqrt 2\, T)$ in every dimension $d$.
```

```{prf:proof} of [](#prop-frank-wolfe-prescribed-smoothness-comparison)
:nonumber:

The inequality $1 - \sqrt{1 - v} \ge v/2$ gives
$A_d \le \delta y/2 - T y^2/(2\sqrt 2\beta)$ with $y = 1/\sqrt d$, and the maximum of this
quadratic in $y$ is $\beta\delta^2/(4\sqrt 2\, T)$.
```

Their lower bound is the square of the positive part of $A_d$, so at fixed $\beta$ and $D$ it
is of order $1/T^2$, while [](#thm-frank-wolfe-prescribed-smoothness-main) gives order $1/T$.

Lower bounds on the simplex [@lan2013complexity; @jaggi2013revisiting] rest on the sparsity of
the iterates; here the output may be any point. For strongly convex sets, the randomized lower
bound of @pokutta2026lower is of order $1/T^2$ (see the entry
[Distributional lower bounds for randomized linear-oracle optimization](../distributional-linear-oracle-lower-bounds/index.md)),
and @halbey2026lower give lower
bounds for vanilla Frank–Wolfe. The hard bodies are not strongly convex, consistent with
[](#thm-frank-wolfe-prescribed-smoothness-linear).

The inner-ball and parallel-body descriptions of smooth sets are classical
[@liu2023gauges; @luner2024performance]. @hazan2026linearly and @liu2023gauges use membership,
gauge or normal information instead of a global LMO, and @garber2015faster relate the progress
of Frank–Wolfe to strong convexity of the set.

## Interactive illustration

The widget runs three methods on a planar smooth body $K + B_r$, where $K$ is a point, a
segment, a triangle or an ellipse, for the objective $\frac12\|x - c\|^2$; drag the point $c$.
*Frank–Wolfe* uses the LMO of the body. *Frank–Wolfe on $K$* is the method of
[](#thm-frank-wolfe-prescribed-smoothness-upper). *Projected gradient* is the method of
[](#thm-frank-wolfe-prescribed-smoothness-linear). The chart shows the primal gap against the
number of oracle calls on logarithmic axes. The dashed lines are the bound $2\delta^2/(t + 1)$
of [](#thm-frank-wolfe-prescribed-smoothness-upper) and, for the disk and the rounded ellipse,
which also have outer tangent balls, the linear rate.

The button *hard body* draws an instance of the hard bodies with $a = r = 1$ in dimension
$256k + 1$. It offers three LMOs: the vertex LMO; an LMO that answers the vertical direction with
the barycenter of the bottom face; and the LMO of a body with perturbed vertices and unique
minimizers. With the barycenter answer, a method that reads $I$ off the answer solves the
instance after one call. With the other two LMOs each call reveals at most one index of $I$. The
dashed horizontal line is the threshold $1/(16k)$ of
[](#thm-frank-wolfe-prescribed-smoothness-vertex) for $T = k - 1$ calls.

```{anywidget} ./widgets/fs.mjs
:css: ./widgets/fs.css
{"body": "segment", "cx": 0.25, "cy": -1.55, "k": 2, "rule": "vertex"}
```

## Not formalized here

The minimax rate for general smooth convex objectives has two terms, $LD^2/T^2$ and
$L(D - 2/\beta)^2/T$. The second is [](#thm-frank-wolfe-prescribed-smoothness-main); the first
follows from the first-order lower bound of @drori2017exact on a ball, which is not formalized
here. The note also contains a second proof of [](#thm-frank-wolfe-prescribed-smoothness-main)
by averaging support functions, and an earlier, weaker estimate with probability $5/42$; the
formal proofs supersede both.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FrankWolfePS/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-prescribed-smoothness.md
```
