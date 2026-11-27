---
title: Frank–Wolfe oracle complexity with prescribed set smoothness
---

```{include} ../_generated/provenance/frank-wolfe-prescribed-smoothness.md
```

How many calls to a linear minimization oracle does a method need on a convex body whose
boundary is smooth? For strongly convex sets the answer is of order $1/\sqrt{\varepsilon}$
[@grimmer2026lower; @pokutta2026lower]. This entry shows that smoothness of the set alone does not
help beyond the trivial reduction: on bodies with $\beta$-Lipschitz unit normals and diameter $D$,
the worst case is of order $L(D-2/\beta)^2/T$ after $T$ calls, uniformly as the dimension grows,
even for a known strongly convex quadratic and even when every linear minimizer is unique. A
matching method, a sliding method for general smooth objectives, and a linear rate for bodies that
are smooth and strongly convex complete the picture. For methods that always return feasible points
the failure probability rises to $3/4$; deterministic methods are defeated in a smaller dimension;
and a distance penalty gives the same order for arbitrary outputs.

:::{note}
A short note on arXiv is in preparation. This page contains the statements and the proofs; every
result is checked in Lean.
:::

Throughout, $\langle\cdot,\cdot\rangle$ is a real inner product, $B_r$ the closed ball of radius
$r$ about $0$ and $\operatorname{diam}$ the diameter. Complexity is measured by the number of
oracle calls a method requires.

## Setting

```{prf:definition} Smooth bodies
:label: def-frank-wolfe-prescribed-smoothness-smooth

A set $C$ is *$\beta$-smooth* if for all $z, w \in C$ and all unit vectors $n, m$ that are outward
normals of $C$ at $z$ and $w$ (that is, $\langle n, y\rangle \le \langle n, z\rangle$ for every
$y \in C$, and likewise for $m$ at $w$),

$$
\|n - m\| \le \beta \|z - w\|.
$$

In particular a boundary point has a single unit outward normal. A direction may still be
minimized by a whole face.
```

```{prf:definition} Exact linear minimization oracle
:label: def-frank-wolfe-prescribed-smoothness-lmo

An *exact linear minimization oracle* for $C$ is a map $O$ such that $O(q) \in C$ and
$\langle q, O(q)\rangle \le \langle q, y\rangle$ for every $y \in C$ and every direction $q$.
For $q = 0$ every point of $C$ qualifies.
```

```{prf:definition} Methods requiring no more than $T$ oracle calls
:label: def-frank-wolfe-prescribed-smoothness-method

A method requiring no more than $T$ calls is a decision tree: it either returns a point (feasible
or not), or asks a direction $q$ and continues, as an arbitrary function of the reply, with a
method requiring no more than $T - 1$ calls. Running it against an oracle $O$ returns a point.
Directions and the output may depend on all previous replies, and evaluations of a known
objective and its gradient are free. A *randomized method* is a family of methods indexed by a
random tape $\omega$, drawn from an arbitrary probability law, independently of the instance.
```

```{prf:definition} Measurable methods
:label: def-frank-wolfe-prescribed-smoothness-measurable

A randomized method is *measurable* if its output is a measurable function of the tape against
every measurable oracle. Methods whose query and output rules are jointly measurable in the tape
and the replies are measurable.
```

```{prf:definition} The hard objective
:label: def-frank-wolfe-prescribed-smoothness-objective

In the ambient space $\mathbb R^{N} \times \mathbb R$, with a horizontal part $x$ and a height
$y$, the hard objective is

$$
f(x, y) = \frac L2\left(\|x\|^2 + y^2\right) + \frac{32L}{\beta}\, y .
$$

It is known to the method. Its Hessian is $L\,\mathrm{Id}$, so it is $L$-smooth and
$L$-strongly convex.
```

## The lower bound, without tie-breaking

(def-frank-wolfe-prescribed-smoothness-unique-oracle)=
If every nonzero direction has exactly one minimizing point on $C$, the oracle has nothing to
choose: it returns that point, and for $q = 0$ a fixed public point $x_0 \in C$.

```{prf:definition} The class
:label: def-frank-wolfe-prescribed-smoothness-class

For $\beta, D > 0$ and a point $x_0$, the class $\mathcal C(\beta, D, x_0)$ consists of the
compact convex bodies $C$ with nonempty interior and $\operatorname{diam} C \le D$ that are
$\beta$-smooth, have exactly one minimizing point for every nonzero direction, and contain $x_0$.
```

```{prf:theorem} No tie-breaking
:label: thm-frank-wolfe-prescribed-smoothness-main

Let $T \ge 0$, $L, \beta > 0$ and $\beta D > 2$, and put $N = 256(T+1)$ and
$x_0 = (a_0 e_1, 0)$ with $a_0 = 0.99\,(D - 2/\beta)/\sqrt 2$. For every measurable randomized
method requiring no more than $T$ oracle calls there is a body $C \subset \mathbb R^{N+1}$ of the
class $\mathcal C(\beta, D, x_0)$, chosen before the tape, such that, against the oracle of $C$,
with probability at least $1/5$ the method returns a point $w$ with

$$
w \notin C \quad\text{or}\quad f(w) - \min_C f \;\ge\; \frac{L(D - 2/\beta)^2}{64(T+1)} .
$$
```

The body depends on the method and on $T$, not on the realized tape. Since the bound holds
with $D$ and $\operatorname{diam} C \le D$, it also holds with $\operatorname{diam} C$ in place of
$D$. Uniqueness of the minimizers is what removes the tie rule: on a body with a flat face some
valid oracle can return a point of the face that encodes the hidden instance, and for the hard
family below one vertical query then reveals everything
({prf:ref}`prop-frank-wolfe-prescribed-smoothness-optimum`). Smoothing that face symmetrically
is not enough either ({prf:ref}`prop-frank-wolfe-prescribed-smoothness-symmetric`); the vertices
must be perturbed.

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-main)
:nonumber:

Write $k = T + 1$ and $r = 1/\beta$, and work first with rounding radius $1$ and simplex scale
$A = 0.99(\beta D - 2)/\sqrt 2$; the general case is the image under $x \mapsto r x$, which turns
radius $1$ into $r$, normals that are $1$-Lipschitz into $\beta$-Lipschitz ones, and the
objective into $f$ up to the factor $L r^2$.

*The family.* The hidden instance is a set $I$ of $8k$ labels containing the anchor $1$, and a
table of grid offsets $Z_j$ for the other labels, each coordinate uniform on
$\sigma\{0, \dots, Q-1\}$, with $\|Z_j\| \le \eta = A^2/(10^6 k (A+36)^2)$. The vertices are
$v_j = (A e_j, 1) + Z_j$. The core is the union of the balls of radius $s(1 - \|u\|^2)$ about
$\sum_j u_j v_j$, over the weights $u$ of the simplex on $I$, and the body is the core plus the
unit ball. The radius is concave in $u$, so the core is convex; minimizing $\langle p, \cdot\rangle$
over the body amounts to minimizing $\langle p, \sum_j u_j v_j\rangle + s\|u\|^2$ over the
simplex, a strictly convex problem with a unique solution, and the minimizing point is unique.

*Coupling with ordered scans.* If a vertex $v_j$ scores more than $2s$ above the best vertex in
the direction $p$, the optimal weights vanish on $j$: moving that weight to the best vertex lowers
the linear term by more than the quadratic term grows. So as long as every label not yet
revealed scores more than $2s$ above the winner, the reply of the full body equals the reply of
the body restricted to the revealed labels and the winner, and the method's whole history is
that of a method on the regular hard family that receives only the winning label of an ordered
scan. The base bound ({prf:ref}`thm-frank-wolfe-prescribed-smoothness-vertex`, in its form for
ordered scans) applies to that method: at least a quarter of the hidden sets make it fail, at
threshold $A^2/(16k)$.

*Few bad tables.* For each prescribed prefix of winning labels, the next direction depends only
on the offsets of labels already revealed. A competing label $j$ has a coordinate where the unit
direction is at least $1/\sqrt N$ in absolute value, and two grid levels there change its score
by more than $4s$; so at most one level puts it within $2s$ of the winner. Summing over all
prefixes, pairs and coordinates, at most a fraction $1/100$ of the tables is bad, for every tape.

*Transfer of the loss.* The two bodies are within $h = 2\eta$ of each other. A feasible output
$w$ of the new body is pulled into the base body by the public repair $(w + h c_0)/(1 + h)$,
$c_0 = (A e_1, 1)$, which moves it by at most $h(2A + 4)$; the objective is $(A + 35)$-Lipschitz on
the relevant region. A base gap of $A^2/(16k)$ at the repaired point therefore leaves a gap of at
least $A^2/(16k) - (A + 35)(2A+5)h \ge A_0^2/(32k)$, $A_0 = A/0.99$, on the new body.

*Averaging.* For every tape, the fraction of failing instances is at least
$\tfrac14 (1 - \tfrac1{100}) \ge \tfrac15$. Integrating over the independent tape and choosing
the best instance gives one body with failure probability at least $1/5$. The diameter is at most
$2 + \sqrt 2 A + 2h \le 2 + \sqrt 2 A_0$, which rescales to $D$; the gap rescales to
$L r^2 A_0^2/(32k) = L(D - 2/\beta)^2/(64k)$.
```

Methods of Frank–Wolfe type return convex combinations of oracle replies and are feasible on
every body. For them the probability is much larger.

```{prf:theorem} Feasible methods, without tie-breaking
:label: thm-frank-wolfe-prescribed-smoothness-unique-feasible

Under the assumptions of [](#thm-frank-wolfe-prescribed-smoothness-main), suppose that the method
returns a point of $C$ against the oracle of $C$, for every body $C$ of the class
$\mathcal C(\beta, D, x_0)$ and every tape. Then some body $C$ of the class, chosen before the
tape, gives

$$
f(w) - \min_C f \;\ge\; \frac{L(D - 2/\beta)^2}{64(T+1)}
$$

with probability at least $3/4$, and expected gap at least $3L(D - 2/\beta)^2/(256(T+1))$.
```

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-unique-feasible)
:nonumber:

The rescaled jittered bodies of the main proof belong to the class, so the method is feasible on
all of them. The repair maps a point of a jittered body into the base body, so the simulated
method of the main proof is feasible on every base instance. For feasible runs the base bound
improves from $1/4$ to $97/128$ ([](#cor-frank-wolfe-prescribed-smoothness-feasible)), for every
tape and every good table. The transfer of the loss is unchanged, and discounting the bad tables
leaves a fraction $\tfrac{97}{128} \cdot \tfrac{99}{100} \ge \tfrac34$ of failing instances.
Integrating over the tape selects one body. On it the gap is nonnegative and bounded, so it is
integrable, and it is at least the threshold on an event of probability at least $3/4$.
```

## The hard family and the vertex rule

```{prf:definition} The hard family
:label: def-frank-wolfe-prescribed-smoothness-family

Let $r = 1/\beta$ and $a = (D - 2/\beta)/\sqrt 2$. For a set $I$ of labels, the hard body is

$$
C_I = \{(a u, r) : u \in \Delta_I\} + B_r ,
$$

the scaled simplex on $I$ at height $r$, rounded by the ball of radius $r$.
```

(def-frank-wolfe-prescribed-smoothness-vertex-oracle)=
The *vertex oracle* answers a direction $q = (q_x, q_y) \ne 0$ with $(a e_j, r) - r q/\|q\|$,
where $j \in I$ minimizes $(q_{x,j}, j)$ lexicographically; the zero direction gets the public
point $(a e_1, 0)$. Minimizing the two summands of $C_I$ separately shows that it is exact.

```{prf:proposition} The hard bodies
:label: prop-frank-wolfe-prescribed-smoothness-family

For $|I| \ge 2$, $C_I$ is compact and convex, has nonempty interior and diameter exactly $D$, and
is $\beta$-smooth; no constant below $\beta$ works. It is not uniformly convex for any modulus.
The vertex oracle is an exact linear minimization oracle.
```

```{prf:proof} of [](#prop-frank-wolfe-prescribed-smoothness-family)
:nonumber:

If $n$ is a unit outward normal at $z = u + b$, $u$ in the core and $\|b\| \le r$, comparing with
$u + r n$ gives $b = r n$, and $u$ maximizes $\langle n, \cdot\rangle$ on the core. For a second
point $w = v + r m$, $\langle n - m, u - v\rangle \ge 0$, hence
$r\|n - m\|^2 \le \langle n - m, z - w\rangle \le \|n - m\|\|z - w\|$. The points above and below
a core point have normals at distance $2$ and are $2r$ apart, so $1/r$ cannot be lowered. The
simplex has diameter $\sqrt 2 a$, attained by two vertices; extending that segment by $r$ at both
ends attains $2r + \sqrt 2 a = D$. Two bottom points $(a e_i, 0)$, $(a e_j, 0)$ have their
midpoint at height $0$, the lowest height in $C_I$, so no ball about it fits, as uniform convexity
would require.
```

```{prf:theorem} With a vertex tie rule
:label: thm-frank-wolfe-prescribed-smoothness-vertex

Under the assumptions of [](#thm-frank-wolfe-prescribed-smoothness-main), with
$N = 256(T + 1)$ labels and the vertex oracle, there is a set $I$ of $8(T+1)$ labels containing the
anchor, chosen before the tape, such that $C_I$ has diameter exactly $D$, is $\beta$-smooth, and
with probability at least $1/4$ the method returns $w \notin C_I$ or
$f(w) - \min_{C_I} f \ge L(D - 2/\beta)^2/(32(T+1))$.
```

```{prf:lemma} The posterior
:label: lem-frank-wolfe-prescribed-smoothness-posterior

Fix the tape and run the method against the vertex oracle on a hidden set drawn uniformly from the
$8(T+1)$-sets of $N = 256(T+1)$ labels that contain the anchor. At every transcript the hidden
sets consistent with it are exactly the completions $P \cup S$ of the labels $P$ known present by
$h$-subsets $S$ of the untested labels $U$, all equally likely. At the end, $|P| \le T + 1$ and

$$
\mathbb E\left[\frac{h}{|U|}\right] = \frac{8(T+1) - 1}{256(T+1) - 1} \le \frac1{32}.
$$
```

```{prf:proof} of [](#lem-frank-wolfe-prescribed-smoothness-posterior)
:nonumber:

A transcript records, for every scanned label, whether it lies in the hidden set; two hidden
sets give the same numerical replies exactly when they agree on these literals, and every
completion has the same prior mass. A fresh test is positive with probability $h/|U|$, after which
the ratio is $(h-1)/(|U|-1)$, and negative otherwise, after which it is $h/(|U|-1)$; the weighted
mean is $h/|U|$. In counting form: over the $\binom{|U|}{h}$ completions the ratios sum to
$\binom{|U|-1}{h-1}$, and both counts split by Pascal's rule along each probe. Each call
records at most one new present label.
```

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-vertex)
:nonumber:

Fix the tape. A nonzero query scans its labels in the order of $(q_{x,j}, j)$ and the reply
determines the first label of $I$ in that order, and nothing else; the zero query reveals nothing.
So the method is a membership decision tree: each scan records absent labels for free and one
present label per call. At any transcript, with $P$ the labels known present, $U$ the unresolved
ones and $h = 8k - |P|$, the hidden sets consistent with it are exactly $P \cup S$ for the
$h$-subsets $S$ of $U$, all with the same prior mass. A fixed unresolved label lies in
$\binom{|U|-1}{h-1}$ of them, so its posterior probability is $h/|U|$; along a probe these counts
split by Pascal's rule.

If $Z = (x, y) \in C_I$, some $u \in \Delta_I$ has $\|x - a u\|^2 + (y - r)^2 \le r^2$, hence
$\|x - a u\|^2 \le 2 r y$. The barycenter gives $\min_{C_I} f \le La^2/(16k)$. If
$\|x\| \ge a/(2\sqrt k)$, then $f(Z) \ge La^2/(8k)$. Otherwise put $w_i = |x_i|/a$, so
$k\|w\|^2 \le 1/4$; if $M = \sum_{i \in I} w_i \le 3/4$, every simplex witness has
$\sum_{i \in I}(a u_i - x_i) \ge a/4$, and Cauchy–Schwarz gives $a^2/(16 \cdot 8k) \le 2 r y$, so
$f(Z) \ge 32 L r y \ge La^2/(8k)$. Either way a feasible $Z$ with $M \le 3/4$ fails.

Summing the posterior estimate $p_i w_i \le p_i^2/(4k) + k w_i^2$ over the leaves of the decision
tree, with the Pascal recursion for the two binomial weights, gives $\mathbb E M \le 9/16$, so
$M \le 3/4$ with probability at least $1/4$ under the uniform prior, for every tape. Integrating
over the independent tape selects one instance. With $r = 1/\beta$ and $a = (D - 2/\beta)/\sqrt 2$
the threshold $La^2/(16k)$ is $L(D - 2/\beta)^2/(32k)$.
```

```{prf:corollary} Feasible methods
:label: cor-frank-wolfe-prescribed-smoothness-feasible

If the method returns feasible points on every instance of the hard family, some instance, chosen
before the tape, gives $f(w) - \min_{C_I} f \ge L(D - 2/\beta)^2/(32(T+1))$ with probability at
least $3/4$, and expected gap at least $3L(D - 2/\beta)^2/(128(T+1))$.
```

```{prf:proof} of [](#cor-frank-wolfe-prescribed-smoothness-feasible)
:nonumber:

Fix the tape. All hidden sets with the same final transcript get the same output $Z$, and $Z$ is
feasible for each of them. If one of them, $J$, is light ($M_J \le 3/4$), the height argument on
$J$ gives $f(Z) \ge La^2/(8k)$, so $Z$ fails on every hidden set of the transcript. Such a $J$
exists as soon as $|U| \ge 127k$: then the posterior membership vector has
$\|p\|^2 = |P| + h^2/|U| \le k + 64k/127 < 9k/4$, and summing
$p_i w_i \le p_i^2/(6k) + \tfrac{3k}{2}w_i^2$ shows that the completions have mean mass at most
$3/4$.

Each fresh test removes one label from $U$, and at most $k$ of them are positive, so a path with at
most $128k$ fresh negative tests ends with $|U| \ge 127k$. The number $X$ of fresh negative tests
obeys an exact potential: summed over the $\binom{|U|}{h}$ completions, a run with $t$ calls left
makes at most $t\binom{|U|}{h+1}$ of them. A fresh test splits both binomials by Pascal's rule; a
negative answer costs one exclusion and keeps the calls, a positive one costs a call. At the start
this is $31T$ per completion, so at most a fraction $31T/(128k) < 31/128$ of the instances end with
more than $128k$ exclusions, and at least $97/128 \ge 3/4$ of them fail. Integrating over the tape
selects one instance; the gap there is nonnegative and bounded, which gives the expectation.
```

The note's Appendix A has $5/7$ here; it discards the transcripts with many exclusions by Markov's
inequality on a cruder bound.

```{prf:theorem} Deterministic methods
:label: thm-frank-wolfe-prescribed-smoothness-deterministic

Let $N = 64(T+1)$. For every deterministic method requiring no more than $T$ calls to the vertex
oracle there is a set $I$ of $8(T+1)$ labels containing the anchor such that $C_I$ has diameter
exactly $D$ and the method returns $w \notin C_I$ or
$f(w) - \min_{C_I} f \ge L(D - 2/\beta)^2/(32(T+1))$.
```

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-deterministic)
:nonumber:

Answer every nonzero query by the first label of its scan order and declare that label present.
After at most $T$ calls at most $k$ labels are declared, the anchor included, and every hidden set
containing them gives exactly this run, hence the same output. Complete the declared labels by a
uniform set of the remaining $N - b \ge 63k$ labels: the membership vector has
$\|p\|^2 \le k + 64k/63 < 9k/4$, so some completion is light, and the output fails on it. For
randomized methods the completion would depend on the tape, which is why they need the larger
dimension.
```

(def-frank-wolfe-prescribed-smoothness-penalized)=
Grimmer and Liu also measure an output by a distance penalty [@grimmer2026lower]. For a weight
$\rho > 0$ the *penalized error* of a point $w$ on $C_I$ is

$$
E_I(w) = f(w) - \min_{C_I} f + \rho\,\operatorname{dist}(w, C_I) .
$$

```{prf:theorem} A distance penalty
:label: thm-frank-wolfe-prescribed-smoothness-penalty

Under the assumptions of [](#thm-frank-wolfe-prescribed-smoothness-vertex), let
$\rho \ge L(2D + 32/\beta)$. No feasibility is assumed. Some instance, chosen before the tape,
has $E_I(w) \ge L(D - 2/\beta)^2/(256(T+1))$ with probability at least $1/4$, and the mean of
$E_I(w)$, a number in $[0, \infty]$, is at least $L(D - 2/\beta)^2/(1024(T+1))$.
```

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-penalty)
:nonumber:

Let $v$ be the point of $C_I$ nearest to $w$ and $\delta = \|w - v\|$. On $C_I$ the gradient of
$f$ has norm at most $L(a + 34r)$, so convexity at $v$ gives
$E_I(w) \ge f(v) - \min_{C_I} f + La\delta$; the weight $\rho \ge L(2D + 32/\beta)$ exceeds
$L(2a + 34r)$. In units where $a = L = 1$ the claim is $E_I \ge 1/(128k)$ on the light event
$M \le 3/4$, which has prior probability at least $1/4$ for every tape. If
$\delta \ge 1/(128k)$ this holds already. Otherwise, if $\|w_x\|^2 > 1/(4k)$, then
$\|v_x\|^2 \ge 9/(64k)$ and $f(v) \ge 9/(128k)$. If not, $\sum_{i \in I} v_i \le 3/4 + \sqrt{8k}\,\delta
\le 4/5$, and the height argument gives $f(v) \ge 2/(25k)$. Subtracting
$\min_{C_I} f \le 1/(16k)$ leaves at least $1/(128k)$ in both cases. Averaging over the tape
selects one instance, and Markov's inequality gives the mean.
```

```{prf:proposition} The optimum
:label: prop-frank-wolfe-prescribed-smoothness-optimum

Let $c = (0, -32 r)$ and $b_0 = (a \mathbf 1_I/|I|, r)$, and $H = \|b_0 - c\|$. The point
$z^\star = b_0 + (r/H)(c - b_0)$ minimizes $f$ on $C_I$. For $|I| \ge 2$, local dual sharpness
in the sense of @pokutta2026frank (see
[Frank–Wolfe beyond 1/t under local dual sharpness](../frank-wolfe-local-dual-sharpness/index.md))
fails at $z^\star$ for the vertex oracle: for every $A > 0$, every exponent $q$ and every set $M \ni z^\star$, there is no
neighbourhood on which $A\|g\|\|x - \mathrm{lmo}(g)\|^q \le \langle g, x - \mathrm{lmo}(g)\rangle$
for all $g$.
```

```{prf:proof} of [](#prop-frank-wolfe-prescribed-smoothness-optimum)
:nonumber:

Up to a constant, $f = \frac L2\|\cdot - c\|^2$. Every core point $v$ satisfies
$\langle v - b_0, b_0 - c\rangle = 0$, because $b_0 - c = (a\mathbf 1_I/|I|, 33 r)$ and the weights
of $v$ sum to one. For $z = v + b \in C_I$, $\|b\| \le r$, this gives
$H\|z - c\| \ge \langle z - c, b_0 - c\rangle \ge H^2 - rH$, so $\|z - c\| \ge H - r = \|z^\star - c\|$.
For the direction $g = b_0 - c$, parallel to $\nabla f(z^\star)$, every horizontal coordinate on $I$
is the same, the oracle returns $(a e_j, r) - r g/H$ for a single label $j$, and
$z^\star - \mathrm{lmo}(g) = b_0 - (a e_j, r) \ne 0$ while
$\langle g, z^\star - \mathrm{lmo}(g)\rangle = 0$.
```

So the instances of the family are outside the $o(1/t)$ guarantees under local dual sharpness,
as they must be. A different valid oracle
could return the barycenter $(a\mathbf 1_I/|I|, 0)$ of the bottom face for the vertical direction,
whose support is $I$: one call would reveal the instance. This is why the tie rule matters for the
hard family, and why the main theorem uses bodies with unique minimizers.

```{prf:proposition} Symmetric bulging reveals the hidden set
:label: prop-frank-wolfe-prescribed-smoothness-symmetric

Without perturbing the vertices, the bulged body of the main proof has a unique lowest point; its
horizontal coordinates are $A/|I|$ on $I$ and $0$ elsewhere.
```

```{prf:proof} of [](#prop-frank-wolfe-prescribed-smoothness-symmetric)
:nonumber:

All vertices $(A e_j, 1)$ have height $1$, so in the vertical direction the weights minimize
$1 + s\|u\|^2$ over the simplex on $I$; the unique minimizer is the uniform weight, by
Cauchy–Schwarz. The lowest point lies below the corresponding center.
```

## Upper bounds

```{prf:lemma} Rolling ball and parallel body
:label: lem-frank-wolfe-prescribed-smoothness-rolling

Let $C$ be a compact convex $\beta$-smooth body and $r = 1/\beta$. Every unit outward normal $n$ at
$z \in C$ gives $z - r n + B_r \subseteq C$. With the erosion $K = \{a : a + B_r \subseteq C\}$,
$C = K + B_r$ and $\operatorname{diam} C = 2r + \operatorname{diam} K$.
```

```{prf:proof} of [](#lem-frank-wolfe-prescribed-smoothness-rolling)
:nonumber:

If $z - rn + B_r$ left $C$, take a point $p$ of that ball farthest from $C$, at distance $d > 0$,
and its nearest point $y \in C$, with unit normal $m = (p - y)/d$. Then $p$ maximizes
$\langle m, \cdot\rangle$ on the ball, so $p = z - rn + rm$, and
$r^2\|m - n\|^2 = \|y - z\|^2 + 2d\langle m, y - z\rangle + d^2 > \|y - z\|^2$, contradicting
smoothness. The erosion is compact and convex, every support point of $C$ is in $K + B_r$, and
separation gives $C = K + B_r$; extending a diametral segment of $K$ gives the diameter.
```

A linear minimization oracle of $C$ yields one for $K$: for $q \ne 0$ and any minimizer $s$ on
$C$, $s + r q/\|q\|$ minimizes on $K$. So Frank–Wolfe can run on $K$ and lift each iterate by
the exact minimization over the ball.

(def-frank-wolfe-prescribed-smoothness-quadratic-method)=
The *quadratic method* for $f(x) = \frac L2\|x - u\|^2$ asks one direction $e \ne 0$ to find a core
point, then performs $T - 1$ Frank–Wolfe steps with step sizes $2/(j+2)$ on $K$, asking the oracle
once per step, and returns the iterate plus its projection correction onto the ball.

```{prf:theorem} The matching upper bound
:label: thm-frank-wolfe-prescribed-smoothness-upper

For $T \ge 2$ the quadratic method requires no more than $T$ oracle calls and no gradient. On
every compact convex $\beta$-smooth body with $\operatorname{diam} C \ge 2/\beta$ and for every
exact oracle it returns a feasible point with

$$
\frac L2\|x - u\|^2 - \min_{w \in C} \frac L2\|w - u\|^2 \;\le\; \frac{2L(\operatorname{diam} C - 2/\beta)^2}{T + 1}.
$$
```

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-upper)
:nonumber:

The envelope $F(a) = \min_{b \in B_r} f(a + b)$ has the gradient $\nabla f(a + b_a)$ and satisfies
the affine lower and the quadratic upper model of $f$ on $K$, which has diameter
$\delta = \operatorname{diam} C - 2r$. The usual Frank–Wolfe recursion
$h_{j+1} \le (1 - \gamma_j) h_j + L\delta^2\gamma_j^2/2$, with a full first step, gives
$h_j \le 2L\delta^2/(j + 2)$, and $T - 1$ steps after the first call give the bound.
```

With [](#thm-frank-wolfe-prescribed-smoothness-main), the hard objective is of this form, so in
the class of $\beta$-smooth bodies of diameter at most $D$ the worst case after $T$ calls is
between $L(D - 2/\beta)^2/(64(T+1))$ (with probability $1/5$) and $2L(D-2/\beta)^2/(T+1)$.

(def-frank-wolfe-prescribed-smoothness-sliding)=
For a general convex objective the entry formalizes a *sliding method* on the product
$K \times B_r$ with the parameters of @lan2016conditional: each outer step makes one gradient
evaluation and solves the proximal subproblem on $K$ by Frank–Wolfe with exact line search and a
Wolfe-gap stopping test, the ball component exactly by radial clipping.

```{prf:theorem} Sliding for smooth convex objectives
:label: thm-frank-wolfe-prescribed-smoothness-sliding

Let $f$ be differentiable and convex with $L$-Lipschitz gradient, and $C$ compact, convex and
$\beta$-smooth with $\operatorname{diam} C \ge 2/\beta$; let $\delta = \operatorname{diam} C - 2/\beta$
and $A = \delta^2 + 4/\beta^2$. For $n \ge 1$ the sliding method makes exactly $n$ gradient
evaluations, requires no more than $1 + n + 9\delta^2 n(n+1)/A$ oracle calls, and returns a
feasible point with gap at most $15 L A/((n + 1)(n + 2))$.
```

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-sliding)
:nonumber:

The product objective $g(a, b) = f(a + b)$ is $2L$-smooth. With
$\gamma_j = 3/(j+2)$, $\tau_j = 6L/(j+1)$ and tolerances $\eta_j = 2LA/(j(j+1))$, the three-point
inequality gives
$h_j \le (1 - \gamma_j)h_{j-1} + \gamma_j\eta_j + \tfrac{\gamma_j\tau_j}2(d_{j-1} - d_j)$, which
telescopes with the weights $j(j+1)(j+2)$. An inner subproblem with $H = \tau\delta^2$ needs no
more than $1 + 6H/\eta$ oracle calls: one atom certifies it when $H \le \eta$, and otherwise exact
line search reaches accuracy $\eta$ within $\lceil 2H/\eta\rceil$ steps and then each failed test
lowers the objective by $\eta^2/(2H)$.
```

(def-frank-wolfe-prescribed-smoothness-joint)=
For bodies that are both smooth and strongly convex the *joint method* keeps a core point $a$ and
an iterate $x \in a + B_r$; each iteration evaluates $g = \nabla f(x)$, sets $u = x - g/L$, asks
the oracle once in the direction $a - u$ unless $u$ is already within $r$ of $a$, moves $a$ by exact
line search, and projects $u$ onto the ball about the new core point.

```{prf:theorem} A linear rate with inner and outer tangent balls
:label: thm-frank-wolfe-prescribed-smoothness-linear

Suppose every support point $s$ of $C$ with unit normal $n$ satisfies
$s - rn + B_r \subseteq C \subseteq s - Rn + B_R$, $0 < r \le R$, and that $f$ is $\mu$-strongly
convex with $L$-Lipschitz gradient. Put $c = \tfrac12\min\{1, r/(2(R - r))\}$ for $R > r$ and
$c = 1$ for $R = r$. After $n$ iterations, each with one gradient and no more than one oracle
call (a single call in total in the ball variant when $R = r$ is known), the joint method returns a
feasible point with

$$
f(x_n) - \min_C f \le \left(1 - c\,\frac{\mu}{L}\right)^n \frac{L(\operatorname{diam} C)^2}{2}.
$$
```

```{prf:proof} of [](#thm-frank-wolfe-prescribed-smoothness-linear)
:nonumber:

The outer ball at the core's support point gives $2(R - r)G \ge \|q\|\,\|s - a\|^2$ for the
Frank–Wolfe gap $G$ of the half squared distance to $u$, so the line search contracts that model
by the factor $1 - c$ relative to any core point. The function
$t \mapsto \tfrac12(\max\{0, \sqrt{2t} - r\})^2$ is convex and nondecreasing and turns this into
$Q(x') \le (1 - c)Q(x) + cQ(z)$ for every $z \in C$, $Q = \tfrac12\|\cdot - u\|^2$. Strong
convexity at $x$ and the upper model at $x'$ then give
$f(x') - f(w) \le (1 - c\mu/L)(f(x) - f(w))$, and the first step starts at $LD^2/2$.
```

## Comparison with earlier bounds

```{prf:proposition} The bound of Grimmer and Liu at fixed parameters
:label: prop-frank-wolfe-prescribed-smoothness-comparison

For $d > T > 0$, $\delta \ge 0$ and $\beta > 0$, the expression in the dimension-dependent bound
of @grimmer2026lower for smooth sets,

$$
A_d = \frac{\delta}{2\sqrt d}\sqrt{1 - T/d} - \frac{1 - \sqrt{1 - T/d}}{\sqrt 2\,\beta},
$$

satisfies $A_d \le \beta\delta^2/(4\sqrt 2\, T)$, whatever the dimension.
```

```{prf:proof} of [](#prop-frank-wolfe-prescribed-smoothness-comparison)
:nonumber:

$1 - \sqrt{1 - u} \ge u/2$ gives $A_d \le \delta y/2 - T y^2/(2\sqrt 2\beta)$ with $y = 1/\sqrt d$,
and the maximum of this quadratic in $y$ is $\beta\delta^2/(4\sqrt 2\, T)$.
```

Their bound is the square of the positive part of $A_d$, so at fixed $\beta$ and $D$ it is of
order $1/T^2$, while [](#thm-frank-wolfe-prescribed-smoothness-main) gives order $1/T$. Lower
bounds on the simplex [@lan2013complexity; @jaggi2013revisiting] rest on sparsity of the iterates;
here the output may be any point. For strongly convex sets, the randomized lower bound of
@pokutta2026lower is of order $1/T^2$ (see
[](#thm-distributional-linear-oracle-lower-bounds-main)), and @halbey2026lower bound vanilla
Frank–Wolfe; the hard family here is not uniformly convex, consistent with
[](#thm-frank-wolfe-prescribed-smoothness-linear). The rolling-ball and parallel-body
characterizations of smooth sets are classical [@liu2023gauges; @luner2024performance];
@hazan2026linearly and @liu2023gauges use membership, gauge or normal information instead of a
global linear oracle, and @garber2015faster relate Frank–Wolfe progress to strong convexity of the
set.

## Watching the rates

Below, the methods run on a planar smooth body $K + B_r$ (a point, a segment, a triangle or an
ellipse rounded by a disk) for $f(x) = \frac12\|x - c\|^2$; drag the target $c$. Vanilla
Frank–Wolfe uses the body's oracle directly, the quadratic method of
[](#thm-frank-wolfe-prescribed-smoothness-upper) works on the core $K$ with step sizes
$2/(j+2)$, and the joint method of [](#thm-frank-wolfe-prescribed-smoothness-linear) uses exact
line search on $K$. The chart plots the gap against the number of oracle calls on logarithmic
axes; dashed are the guarantee $2\delta^2/(t+2)$ and, for the disk and the rounded ellipse, which
also have outer tangent balls, the linear rate.

The button *hard family* draws a hidden instance of the hard family with $a = r = 1$ in dimension
$256k + 1$. The quadratic method starts with the vertical direction; *probe, then exploit* does
the same but reads the hidden set off the reply whenever it can. Under the barycenter rule the
reply is the barycenter of the bottom face and the instance is solved after one call. Under the
vertex rule, or with the unique oracle of a jittered body, each call reveals at most one hidden
label, and the methods follow the order $1/t$; the dashed level is the threshold $1/(16k)$ of
[](#thm-frank-wolfe-prescribed-smoothness-vertex) for $T = k - 1$ calls.

```{anywidget} ./widgets/fs.mjs
:css: ./widgets/fs.css
{"body": "segment", "cx": 0.25, "cy": -1.55, "k": 2, "rule": "vertex"}
```

## Not formalized here

The minimax claim for general smooth objectives needs both terms $LD^2/T^2$ and
$L(D-2/\beta)^2/T$; the second is [](#thm-frank-wolfe-prescribed-smoothness-main), the first is
the first-order lower bound of @drori2017exact on a ball, which is not formalized here. The note
also contains a second proof of the unique-minimizer bound by averaging support functions, and an
audit of an earlier estimate with probability $5/42$; both are superseded by the formal proofs.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FrankWolfePS/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-prescribed-smoothness.md
```
