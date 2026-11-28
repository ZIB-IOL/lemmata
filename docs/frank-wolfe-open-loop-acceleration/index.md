---
title: "Acceleration of Frank–Wolfe algorithms with open-loop step-sizes"
numbering:
  headings: false
---

```{include} ../_generated/provenance/frank-wolfe-open-loop-acceleration.md
```

:::{note}
This entry formalizes the paper *Acceleration of Frank–Wolfe Algorithms with Open-Loop Step-Sizes*
by Elias Wirth, Thomas Kerdreux and Sebastian Pokutta [@wirth2022acceleration], currently its
Sections 3 to 5; numbers refer to the arXiv version.
:::

:::{admonition} Errata
:class: warning

**Lemma 3.2.** The scaling inequality
$\langle \nabla f(x), x - p\rangle / \|x - p\|_2 \ge (\beta/\delta) \|\nabla f(x)\|_2$ fails when
$C$ is not full-dimensional: the component of $\nabla f(x)$ orthogonal to $\operatorname{aff}(C)$
does not change the left side. For $C = [-1, 1] \times \{0\}$, $f(x) = x_1^2/2 + 10 x_2$, $x^* = 0$,
$\beta = 1$ and $\delta = 2$, the point $x = (1/2, 0)$ has the atom $p = (-1, 0)$, and the left side
is $1/2$ while the right side is $\sqrt{100.25}/2 > 5$. With the gradient restricted to the
directions of $\operatorname{aff}(C)$ the lemma holds, and Theorem 3.6 follows as stated.

**Algorithm 4, the first iterate.** Line 1 sets $x_1$ to a Frank–Wolfe vertex for $\nabla f(x_0)$,
and the loop, which starts at $t = 0$, sets $x_1$ again by a pairwise step from $x_0$. That step can
leave $C$: on $C = \operatorname{conv}\{e_1, e_2\}$ with $f(x) = x_2$ and $x_0 = (0.3, 0.7)$, the
step size is $\gamma_0 = 1$, the vertices are $p_0^+ = e_1$ and $p_0^- = e_2$, and
$x_1 = (1.3, -0.3) \notin C$. As in Garber and Meshi [@garber2016linear], the formal run takes the
Frank–Wolfe vertex as $x_1$ and starts the pairwise steps at $t = 1$; the proofs of the paper use
this reading.
:::

The Frank–Wolfe algorithm with line search or short steps adapts to the problem: on structured
instances it converges linearly. With the open-loop step sizes $\eta_t = \ell/(t + \ell)$, which
need no knowledge of the function and no line search, the classical analysis only gives $O(1/t)$.
The paper shows that open-loop step sizes accelerate as well, to rates up to $O(1/t^2)$, whenever
the primal gaps obey a recursion of the form
$h_{t+1} \le (1 - \eta_t/2) h_t - \eta_t A C_t h_t^{1 - \psi} + \eta_t^2 B C_t$. Such a recursion
follows from a *scaling inequality*, a lower bound on the Frank–Wolfe gap in terms of the primal
gap, and the paper derives one for each of three settings: minimizers in the relative interior,
gradients bounded away from zero on a uniformly convex set, and a Hölderian error bound on a
uniformly convex set.

The statements hold in real normed spaces, for every Frank–Wolfe run, with any tie-breaking in the
linear minimization oracle. Runs, smoothness over the feasible region and Hölderian error bounds are
the objects of [Frank–Wolfe: the core](../frank-wolfe-core/index.md). Throughout,
$h_t = f(x_t) - f(x^\star)$ is the primal gap, $\delta$ the diameter of the feasible region $C$, and
$f$ is convex over $C$ and differentiable at the points of $C$.

## The baseline rate

```{prf:definition} Open-loop step sizes
:label: def-frank-wolfe-open-loop-acceleration-eta
:nonumber:

For $\ell > 0$, $\eta_t = \ell/(t + \ell)$ for every integer $t$. The paper evaluates it at negative
indices as well, such as $\eta_{-1} = \ell/(\ell - 1)$; this section uses $\ell = 4$.
```

```{prf:proposition} Convergence rate of order $O(1/t)$
:label: prop-frank-wolfe-open-loop-acceleration-baseline
:enumerator: 3.1

Let $C$ be compact and $f$ $L$-smooth over $C$. Every Frank–Wolfe run with $\eta_t = 4/(t + 4)$
satisfies $h_t \le 8L\delta^2/(t + 3)$ for all $t \ge 1$.
```

Smoothness gives the progress bound
$h_{t+1} \le h_t - \eta_t \langle \nabla f(x_t), x_t - p_t\rangle + \eta_t^2 L \|x_t - p_t\|^2/2$,
and the Frank–Wolfe gap is at least $h_t$, so $h_{t+1} \le (1 - \eta_t) h_t + \eta_t^2 L\delta^2/2$.
Since $\eta_0 = 1$, $h_1 \le L\delta^2/2$, and the bound follows by induction.

## A blueprint for acceleration

The progress bound subtracts $\eta_t$ times the Frank–Wolfe gap. A scaling inequality bounds that
gap below by a power of the primal gap, and Lemma 3.5 turns the resulting recursion into a rate. For
minimizers in the relative interior, the geometry of $C$ gives the first scaling inequality.

```{prf:lemma} Scaling in the relative interior, corrected
:label: lem-frank-wolfe-open-loop-acceleration-gm
:enumerator: 3.2

Let $C$ be compact, $x^\star$ a minimizer and $\beta > 0$ such that every point of
$\operatorname{aff}(C)$ within distance $\beta$ of $x^\star$ lies in $C$. For every $x \in C$, every
$p \in \operatorname{argmin}_{v \in C} f'(x)(v)$ and every direction $u$ of $\operatorname{aff}(C)$
with $\|u\| \le 1$, $\beta \|x - p\| f'(x)(u) \le \delta f'(x)(x - p)$.
```

In a Euclidean space, the supremum of $f'(x)(u)$ over these $u$ is the norm of the gradient
projected onto the directions of $\operatorname{aff}(C)$; the paper uses $\|\nabla f(x)\|_2$
instead, which is wrong for lower-dimensional $C$ (see the errata). The proof compares $p$ with the
point $x^\star - \beta u \in C$: $f'(x)(x - p) \ge f'(x)(x - x^\star) + \beta f'(x)(u)$, and the
first term is nonnegative by convexity.

```{prf:lemma} The iterates approach the minimizers
:label: lem-frank-wolfe-open-loop-acceleration-near
:enumerator: 3.3

Let $C$ be compact, $f$ $L$-smooth over $C$ with $L > 0$ and $\delta > 0$, with a
$(\mu, \theta)$-Hölderian error bound, $\mu, \theta > 0$, and let $\beta > 0$. Every Frank–Wolfe run
with $\eta_t = 4/(t + 4)$ is within distance $\beta$ of the minimizers for all
$t \ge \lceil 8L\delta^2 (\mu/\beta)^{1/\theta} \rceil$.
```

The second scaling inequality comes from the error bound.

```{prf:lemma} Scaling from a Hölderian error bound
:label: lem-frank-wolfe-open-loop-acceleration-scaling-heb
:enumerator: 3.4

Let $C$ be compact and let $f$ have the unique minimizer $x^\star$ and a $(\mu, \theta)$-Hölderian
error bound with $\mu > 0$. For $x \in C \setminus \{x^\star\}$,
$h^{1 - \theta}/\mu \le f'(x)(x - x^\star)/\|x - x^\star\| \le \|f'(x)\|$, where
$h = f(x) - f(x^\star)$.
```

The core proves the same inequality without uniqueness, for a nearest minimizer.

```{prf:lemma} The sequence lemma
:label: lem-frank-wolfe-open-loop-acceleration-sequence
:enumerator: 3.5

Let $\psi \in [0, 1/2]$, $S \ge 1$, $A, B, C > 0$, $0 \le C_t \le C$ and $h_t \ge 0$ with
$h_{t+1} \le (1 - \eta_t/2) h_t - \eta_t A C_t h_t^{1-\psi} + \eta_t^2 B C_t$ for $S \le t < T$,
where $\eta_t = 4/(t + 4)$. Then for $S \le t \le T$,

$$
h_t \le \max\left\{ \left(\frac{\eta_{t-2}}{\eta_{S-1}}\right)^{1/(1-\psi)} h_S,\
\left(\frac{\eta_{t-2} B}{A}\right)^{1/(1-\psi)} + \eta_{t-2}^2 B C \right\}.
$$
```

The induction proves the sharper bound with $\eta_{t-2}\eta_{t-1}$ in place of $\eta_{t-2}^2$ and
exponent $1/(2(1-\psi))$. If $h_t$ is at most $(\eta_t B/A)^{1/(1-\psi)}$, the recursion adds at
most $\eta_t^2 BC$. Otherwise the two last terms cancel, and $1 - \eta_t/2 = \eta_t/\eta_{t-2}$
moves the bound from $t$ to $t + 1$, because $r \le r^e$ for $r = \eta_t/\eta_{t-2} \le 1$ and
$e \le 1$.

```{prf:theorem} Minimizers in the relative interior
:label: thm-frank-wolfe-open-loop-acceleration-interior
:enumerator: 3.6

Let $C$ be compact with $\delta > 0$, $f$ $L$-smooth over $C$ with $L > 0$ and with a
$(\mu, \theta)$-Hölderian error bound, $\mu > 0$, $\theta \in [0, 1/2]$, and let $\beta > 0$ be such
that every point of $\operatorname{aff}(C)$ within distance $\beta$ of a minimizer lies in $C$.
Every Frank–Wolfe run with $\eta_t = 4/(t + 4)$ satisfies, for every $S \ge 1$ and all $t \ge S$,

$$
h_t \le \max\left\{ \left(\frac{\eta_{t-2}}{\eta_{S-1}}\right)^{1/(1-\theta)} h_S,\
\left(\eta_{t-2} \frac{2\mu L\delta^3}{\beta^2}\right)^{1/(1-\theta)} + \eta_{t-2}^2
\frac{L\delta^2}{2}
\right\}.
$$
```

The paper states the theorem for $t \ge S = \lceil 8L\delta^2(2\mu/\beta)^{1/\theta} \rceil$, after
which Lemma 3.3 keeps the iterates near $x^\star$. The formal proof needs no such burn-in. Applying
the corrected Lemma 3.2 at a nearest minimizer $y$ with $u = (x - y)/\|x - y\|$ and combining it
with Lemma 3.4 bounds the Frank–Wolfe gap below by $(\beta/\mu) h^{1-\theta}$ at every point of $C$.
Averaged with the bound $h$, this gives the recursion of Lemma 3.5 with $A = \beta^2/(4\mu\delta)$
and $B = L\delta^2/2$, since $2\beta \le \delta$.

The rate is compatible with the lower bound for the probability simplex in $\mathbb{R}^d$, Example
2.7 of [Conditional gradient methods: smoothness, scaling and linear
rates](../conditional-gradient-basics/index.md): as the paper's Lemma 3.7 and Remark 3.8 explain,
there $\beta = 1/d$, and acceleration only starts after $\Omega(d)$ iterations.

## Uniformly convex feasible regions

On a uniformly convex set, the atom is far from the iterate exactly when the Frank–Wolfe gap is
large. The scaling inequality below follows from Proposition 2.19 of [Conditional gradient methods:
smoothness, scaling and linear rates](../conditional-gradient-basics/index.md),
$\alpha \|f'(x)\| \|x - p\|^q \le f'(x)(x - p)$, and the gap bound $h \le f'(x)(x - p)$.

```{prf:lemma} Scaling for uniformly convex sets
:label: lem-frank-wolfe-open-loop-acceleration-scaling-unif
:enumerator: 3.9

Let $C$ be $(\alpha, q)$-uniformly convex with $\alpha > 0$ and $q \ge 2$, and $x^\star$ a
minimizer. For $x \in C$ and $p \in \operatorname{argmin}_{v \in C} f'(x)(v)$,
$(\alpha \|f'(x)\|/2)^{2/q} \, h^{1 - 2/q} \, \|x - p\|^2 \le f'(x)(x - p)$, where
$h = f(x) - f(x^\star)$.
```

```{prf:theorem} Gradients bounded away from zero
:label: thm-frank-wolfe-open-loop-acceleration-exterior
:enumerator: 3.10

Let $C$ be compact and $(\alpha, q)$-uniformly convex with $\delta > 0$, $\alpha > 0$, $q \ge 2$,
and $f$ $L$-smooth over $C$ with $L > 0$ and $\|f'(y)\| \ge \lambda > 0$ on $C$. Every Frank–Wolfe
run with $\eta_t = 4/(t + 4)$ satisfies, if $q \ge 4$, for all $t \ge 1$,

$$
h_t \le \max\left\{ \eta_{t-2}^{1/(1-2/q)} \frac{L\delta^2}{2},\
\left(\eta_{t-2} L \left(\frac{2}{\alpha\lambda}\right)^{2/q}\right)^{1/(1-2/q)} +
\eta_{t-2}^2 \frac{L\delta^2}{2} \right\},
$$

and, if $q < 4$, for all $t \ge S = \lceil 8L\delta^2 \rceil$,

$$
h_t \le \max\left\{ \left(\frac{\eta_{t-2}}{\eta_{S-1}}\right)^2 h_S,\
\left(\eta_{t-2} L \left(\frac{2}{\alpha\lambda}\right)^{2/q}\right)^2 +
\eta_{t-2}^2 \frac{L\delta^2}{2} \right\}.
$$
```

With $C_t = \|x_t - p_t\|^2/2$ the scaling inequality gives the recursion of Lemma 3.5 with
$A = (\alpha\lambda/2)^{2/q}$, $B = L$ and $\psi = 2/q$. For $q < 4$, $\psi > 1/2$, and the proof
waits until Proposition 3.1 gives $h_t \le 1$, from where $h_t^{1-2/q} \ge h_t^{1/2}$.

```{prf:theorem} No assumption on the location of the minimizer
:label: thm-frank-wolfe-open-loop-acceleration-unrestricted
:enumerator: 3.12

Let $C$ be compact and $(\alpha, q)$-uniformly convex with $\delta > 0$, $\alpha > 0$, $q \ge 2$,
and $f$ $L$-smooth over $C$ with $L > 0$ and with a $(\mu, \theta)$-Hölderian error bound,
$\mu > 0$, $\theta \in [0, 1/2]$. Every Frank–Wolfe run with $\eta_t = 4/(t + 4)$ satisfies, for all
$t \ge 1$,

$$
h_t \le \max\left\{ \eta_{t-2}^{1/(1-2\theta/q)} \frac{L\delta^2}{2},\
\left(\eta_{t-2} L \left(\frac{2\mu}{\alpha}\right)^{2/q}\right)^{1/(1-2\theta/q)} +
\eta_{t-2}^2 \frac{L\delta^2}{2} \right\}.
$$
```

Here the error bound replaces the lower bound on the gradient: $\|f'(x)\| \ge h^{1-\theta}/\mu$, and
$\psi = 2\theta/q \le 1/2$.

## Minimizers in the relative interior of a face

When $C$ is a polytope and the minimizer lies in the relative interior of a face $C^\star$ of
dimension at least one, Frank–Wolfe with line search or short steps converges no faster than
$\Omega(1/t^{1+\varepsilon})$ by the lower bound of Wolfe, while the open-loop step sizes reach
$O(1/t^2)$. Write $C = \operatorname{conv} V$ and $C^\star = \operatorname{conv} F$ for a set
$F \subseteq V$ of vertices. *Strict complementarity* asks for $\kappa > 0$ with
$\langle \nabla f(x^\star), p - x^\star \rangle \ge \kappa$ for $p \in V \setminus F$ and
$\langle \nabla f(x^\star), p - x^\star \rangle = 0$ for $p \in F$. The minimizer lies in the
relative interior of the face: $x^\star \in \operatorname{aff}(F)$, and every point of
$\operatorname{aff}(F)$ within distance $\beta > 0$ of $x^\star$ lies in $C$. Besides smoothness
over $C$, the results of this section use that the gradient is $L$-Lipschitz on $C$.

```{prf:lemma} Active set identification
:label: lem-frank-wolfe-open-loop-acceleration-active-set
:enumerator: 4.1

Let $f$ be $L$-smooth over $C$ with $L$-Lipschitz gradient on $C$, $L > 0$ and $\delta > 0$, with
unique minimizer $x^\star$, a $(\mu, \theta)$-Hölderian error bound with $\mu > 0$ and
$\theta \in (0, 1/2]$, and strict complementarity. Every Frank–Wolfe run with $\eta_t = 4/(t + 4)$
has its atoms in $C^\star$ for all
$t \ge \lceil 8L\delta^2 (2\mu L\delta/\kappa)^{1/\theta} \rceil$.
```

From then on, $\mu L\delta h_t^\theta < \kappa/2$ by Proposition 3.1, so the gradient at $x_t$
differs from the one at $x^\star$ by less than $\kappa/2$ on every $p - x_t$. Every vertex outside
$F$ is then worse than every vertex in $F$, and the atom, a convex combination of minimizing
vertices, lies in $\operatorname{conv} F$.

```{prf:lemma} Scaling at the boundary
:label: lem-frank-wolfe-open-loop-acceleration-scaling-boundary
:enumerator: 4.2

Let $x^\star$ be a minimizer in the relative interior of the face as above. For $x \in C$,
$p \in \operatorname{argmin}_{v \in C} f'(x)(v)$ and every direction $u$ of $\operatorname{aff}(F)$
with $\|u\| \le 1$, $\beta f'(x)(u) \le f'(x)(x - p)$.
```

In a Euclidean space, the supremum over such $u$ is $\|\Pi \nabla f(x)\|_2$ for the orthogonal
projection $\Pi$ onto the directions of $\operatorname{aff}(F)$, the form of the paper, which goes
back to Bach.

```{prf:lemma} Distance to the optimal face
:label: lem-frank-wolfe-open-loop-acceleration-distance-face
:enumerator: 4.3

Under the assumptions of Lemma 4.1, with $x^\star \in \operatorname{aff}(F)$ and $\beta > 0$, let
$S$ be the larger of $\lceil 8L\delta^2 (\mu/\beta)^{1/\theta} \rceil$ and
$\lceil 8L\delta^2 (2\mu L\delta/\kappa)^{1/\theta} \rceil$. For all $t \ge S$, the iterates are
within distance $(\eta_t/\eta_S)^4 \beta$ of $\operatorname{aff}(F)$.
```

Once the atoms lie in the face, every step contracts the distance to its affine hull by
$1 - \eta_t$, and $t (t + 5)^4 \le (t + 4)^5$ turns the product of these factors into
$(\eta_t/\eta_S)^4$. Lemma 3.3 starts the induction.

```{prf:lemma} Scaling from strong convexity
:label: lem-frank-wolfe-open-loop-acceleration-scaling-cvx
:enumerator: 4.4

In a real inner product space, let $f$ be $\alpha$-strongly convex on $C$ with $\alpha > 0$,
$L$-smooth over $C$ with $L$-Lipschitz gradient on $C$, $L > 0$, $\delta > 0$, with unique minimizer
$x^\star$ in the relative interior of the face and strict complementarity, and let
$M = \max_{y \in C} \|\nabla f(y)\|$ and $S$ the larger of
$\lceil 16L\delta^2/(\alpha\beta^2) \rceil$ and $\lceil 64L^3\delta^4/(\alpha\kappa^2) \rceil$. For
$t \ge S$, either $h_t \le (\eta_t/\eta_S)^4 \beta M$, or a direction $u$ of $\operatorname{aff}(F)$
with $\|u\| \le 1$ satisfies

$$
f'(x_t)(u) \ge \sqrt{\alpha/2}\,\sqrt{h_t} - \left(\frac{\eta_t}{\eta_S}\right)^2 \sqrt{\alpha\beta
M/2} -
\left(\frac{\eta_t}{\eta_S}\right)^4 L\beta.
$$
```

The orthogonal projection $y_t$ of $x_t$ onto $\operatorname{aff}(F)$ lies within $\beta$ of
$x^\star$, hence in $C$, and within $(\eta_t/\eta_S)^4 \beta$ of $x_t$. Strong convexity at $y_t$,
compared with $x^\star$, bounds the derivative in the direction of $y_t - x^\star$ below by
$\sqrt{\alpha/2}\,\sqrt{f(y_t) - f(x^\star)}$, and the Lipschitz gradient carries the bound back to
$x_t$. Strong convexity provides the error bound with $\mu = \sqrt{2/\alpha}$ and $\theta = 1/2$,
for which $S$ is the threshold of Lemmas 3.3 and 4.1.

```{prf:theorem} Minimizer in the relative interior of a face
:label: thm-frank-wolfe-open-loop-acceleration-face
:enumerator: 4.5

Under the assumptions of Lemma 4.4, let $A = \sqrt{\alpha}\,\beta/(2\sqrt{2})$,
$B = L\delta^2/2 + \beta\sqrt{\alpha\beta M}/(2\sqrt{2}\,\eta_S) + L\beta^2/(2\eta_S)$,
$D = \beta M$ and $E = L\delta^2/2$. Every Frank–Wolfe run with $\eta_t = 4/(t + 4)$ satisfies, for
all $t \ge S$,

$$
h_t \le \eta_{t-2}^2 \max\left\{ \frac{h_S}{\eta_{S-1}^2},\ \frac{B^2}{A^2} + B,\ \frac{D}{\eta_S^2}
+ E \right\}.
$$
```

As long as $h_t > (\eta_t/\eta_S)^4 \beta M$, Lemmas 4.2 and 4.4 give the recursion of Lemma 3.5
with $\psi = 1/2$. The induction carries a third term, $\eta_{t-2}\eta_{t-1}(D/\eta_S^2 + E)$, for
the other iterates.

## Decomposition-invariant pairwise Frank–Wolfe

Section 5 carries the blueprint over to two variants that converge linearly with line search on
polytopes. The first is the decomposition-invariant pairwise Frank–Wolfe algorithm of Garber and
Meshi on a simplex-like polytope $C = \{x \ge 0 \mid Ax = b\}$ with vertices in $\{0, 1\}^d$; its
objects are those of [Conditional gradient methods: away-step, fully-corrective and pairwise
Frank–Wolfe](../away-step-frank-wolfe/index.md). From $x_t$, it moves weight from a vertex $p_t^-$
of the minimal face of $x_t$ that maximizes $\langle \nabla f(x_t), \cdot \rangle$ to a Frank–Wolfe
vertex $p_t^+$, with the step size $\gamma_t$, the largest power of $1/2$ that is at most
$\eta_t = 8/(t + 8)$. Such step sizes keep the run inside $C$.

```{prf:proposition} Convergence rate of order $O(1/t)$
:label: prop-frank-wolfe-open-loop-acceleration-dipfw-baseline
:enumerator: 5.2

Let $C$ be a simplex-like polytope and $f$ $L$-smooth over $C$. Every run of decomposition-invariant
pairwise Frank–Wolfe with these step sizes satisfies $h_t \le 32L\delta^2/(t + 7)$ for all
$t \ge 1$.
```

A pairwise step gains $\gamma_t \langle \nabla f(x_t), p_t^- - p_t^+ \rangle$, at least half of
$\eta_t$ times this pairwise gap. The pairwise gap is at least $h_t$, because $p_t^-$ maximizes the
gradient over the minimal face of $x_t$, whose convex hull contains $x_t$. Hence
$h_{t+1} \le (1 - \eta_t/2) h_t + \eta_t^2 L\delta^2/2$.

```{prf:theorem} Convergence rate of order up to $O(1/t^2)$
:label: thm-frank-wolfe-open-loop-acceleration-dipfw
:enumerator: 5.3

If moreover $\delta > 0$, $L > 0$, and $f$ has a unique minimizer $x^\star$ and a
$(\mu, \theta)$-Hölderian error bound with $\mu > 0$ and $\theta \in [0, 1/2]$, then for all
$t \ge 1$

$$
h_t \le \max\left\{ \eta_{t-2}^{1/(1-\theta)} \frac{L\delta^2}{2},\
\left(\eta_{t-2} \, 2\mu L\delta^2 \sqrt{\|x^\star\|_0}\right)^{1/(1-\theta)} +
\eta_{t-2}^2 \frac{L\delta^2}{2} \right\},
$$

where $\|x^\star\|_0$ is the number of nonzero coordinates of $x^\star$ and $\eta_t = 8/(t + 8)$.
```

The sparsity scaling of Garber and Meshi bounds the pairwise gap below by
$\langle \nabla f(x_t), x_t - x^\star \rangle / (\sqrt{\|x^\star\|_0} \|x_t - x^\star\|)$, and the
error bound turns this into $h_t^{1-\theta}/(\mu\sqrt{\|x^\star\|_0})$. The recursion now contracts
by $1 - \eta_t/4$, which equals $\eta_t/\eta_{t-2}$ for $\eta_t = 8/(t + 8)$; this is why the
section uses $\ell = 8$ (Remark 5.4). The induction of Lemma 3.5 goes through for every $\ell > 2$
with the contraction $1 - (2/\ell)\eta_t$.

## Away-step Frank–Wolfe with open-loop step sizes

Away-step Frank–Wolfe keeps the iterate as a convex combination of an active set of vertices and may
step away from the worst of them. With open-loop step sizes, a step can be cut short to keep the
weights nonnegative, and such a *drop step* removes a vertex. Algorithm 5 therefore counts progress
steps: with $\ell_t$ progress steps so far, the step size is
$\gamma_t = \min\{\eta_{\ell_t}, \gamma_{t,\max}\}$, and the step is a progress step when it does at
least as well, in the smoothness bound, as the full step $\eta_{\ell_t}$.

```{prf:definition} Away-step Frank–Wolfe with open-loop step sizes
:label: def-frank-wolfe-open-loop-acceleration-olafw-step
:nonumber:

From the state $(x, S, \lambda, \ell)$, with a Frank–Wolfe vertex $v$, an away vertex $a \in S$ and
$g = \nabla f(x)$, let $\eta = 4/(\ell + 4)$. If
$\langle g, a - x \rangle \le \langle g, x - v \rangle$, take the Frank–Wolfe step
$x' = x + \gamma(v - x)$ with $\gamma = \min\{\eta, 1\}$; otherwise the away step
$x' = x + \gamma(x - a)$ with $\gamma = \min\{\eta, \lambda_a/(1 - \lambda_a)\}$. Weights and active
set are updated as usual, and $\ell' = \ell + 1$ exactly when
$(\eta - \gamma)\langle g, a - v \rangle \le (\eta^2 - \gamma^2) L\delta^2$.
```

```{prf:definition} Run of away-step Frank–Wolfe with open-loop step sizes
:label: def-frank-wolfe-open-loop-acceleration-olafw-run
:nonumber:

A run starts at a vertex $x_0$ with active set $\{x_0\}$, weight $1$ and $\ell_0 = 0$, and every
step is a step of the definition above, with $\delta$ the diameter of the vertex set, for some
Frank–Wolfe vertex and some away vertex.
```

```{prf:lemma} Drop-step characterization
:label: lem-frank-wolfe-open-loop-acceleration-drop-step
:enumerator: 5.5

Let $A, B > 0$ and $g(\eta) = -\eta A + \eta^2 B$. For $0 \le \gamma \le \eta$, $g(\gamma) \le g(0)$
or $g(\gamma) \le g(\eta)$.
```

So a step that is not a progress step does not increase the primal gap.

```{prf:lemma} Number of progress steps
:label: lem-frank-wolfe-open-loop-acceleration-progress-steps
:enumerator: 5.6

Every run has made at least $\lceil t/2 \rceil$ progress steps before iteration $t$.
```

Steps of full length are progress steps, so every other step is a drop step, which removes a vertex
from the active set. Only Frank–Wolfe steps add vertices, so the formal proof keeps
$|S_t| + t \le 1 + 2\ell_t$.

```{prf:proposition} Convergence rate of order $O(1/t)$
:label: prop-frank-wolfe-open-loop-acceleration-afw-baseline
:enumerator: 5.7

Let $f$ be $L$-smooth over $C = \operatorname{conv} V$. Every run satisfies
$h_t \le 16L\delta^2/(t + 6)$ for all $t \ge 1$.
```

A progress step satisfies $h_{t+1} \le (1 - \eta_{\ell_t}) h_t + \eta_{\ell_t}^2 L\delta^2/2$. For a
drop step that passes the test, this uses that it is an away step: there the away gap exceeds the
Frank–Wolfe gap, so half the sum of both, which the test compares, is still at least $h_t$. Hence
$h_t \le 8L\delta^2/(\ell_t + 3)$, and Lemma 5.6 gives the claim.

The away-step scaling of Lacoste-Julien and Jaggi (Lemma 5.8), the scaling property of the pyramidal
width $\omega$, is formalized in the entry on away-step Frank–Wolfe linked above.

```{prf:theorem} Convergence rate of order up to $O(1/t^2)$
:label: thm-frank-wolfe-open-loop-acceleration-afw
:enumerator: 5.9

If moreover $\delta > 0$, $L > 0$, the pyramidal width $\omega$ of $V$ is positive and $f$ has a
$(\mu, \theta)$-Hölderian error bound with $\mu > 0$ and $\theta \in [0, 1/2]$, then for all
$t \ge 1$ and $k = \lceil t/2 \rceil$,

$$
h_t \le \max\left\{ \eta_{k-2}^{1/(1-\theta)} \frac{L\delta^2}{2},\
\left(\eta_{k-2} \frac{2\mu L\delta^2}{\omega}\right)^{1/(1-\theta)} +
\eta_{k-2}^2 \frac{L\delta^2}{2} \right\}.
$$
```

Along the progress steps, the scaling of the pyramidal width and the error bound give
$\langle \nabla f(x_t), a_t - v_t \rangle \ge (\omega/\mu) h_t^{1-\theta}$, and the primal gaps
follow the recursion of Lemma 3.5 in the number of progress steps. The formal proof carries the
invariant of Lemma 3.5 along the run, advancing it in progress steps only.

:::{note}
**Differences from the paper.**
- The paper works in $\mathbb{R}^d$ with the Euclidean norm and assumes a unique minimizer; the
  formal statements hold in real normed spaces. Apart from Lemma 3.4, which is about the unique
  minimizer, they need no uniqueness: the error bound measures the distance to the set of
  minimizers, Lemma 3.3 bounds that distance, and Theorem 3.6 asks for the ball inside $C$ around
  every minimizer.
- Lemma 3.2 holds for every $x \in C$, not only near $x^\star$, and Theorem 3.6 holds from every
  $S \ge 1$.
- The constant $\lambda$ of Theorem 3.10 is called `ν` in Lean, since `λ` is a keyword.
- Remark 3.11, on rates beyond $O(1/t^2)$ for strongly convex sets, is not formalized.
- In Section 5 the step sizes of decomposition-invariant pairwise Frank–Wolfe are given as powers of
  $1/2$ in $(\eta_t/2, \eta_t]$, which determines them. Theorem 5.9 needs no unique minimizer.
- Section 4 also assumes that the gradient is $L$-Lipschitz on $C$, which the proofs of Lemmas 4.1
  and 4.4 use; the quadratic upper bound over $C$ does not imply it. Lemma 4.2 does not need that
  all minimizers of the linear functional lie in the face. Lemmas 4.1 to 4.3 hold in real normed
  spaces, with the distance to $\operatorname{aff}(F)$ in place of $\|(I - \Pi)(x_t - x^\star)\|_2$,
  and Lemma 4.4 is stated with a direction $u$ in place of the projected gradient. Remark 4.6, on
  relaxing strict complementarity, is not formalized.
:::

## Coverage

This entry covers Sections 3 to 5 of the paper. Kernel herding (Section 6) is out of scope.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FWOpenLoop/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-open-loop-acceleration.md
```
