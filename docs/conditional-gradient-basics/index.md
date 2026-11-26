---
title: "Conditional gradient methods: smoothness, scaling and linear rates"
numbering:
  headings: false
---

```{include} ../_generated/provenance/conditional-gradient-basics.md
```

:::{note}
This entry comes from the book *Conditional Gradient Methods: From Core Principles to AI
Applications* by Gábor Braun, Alejandro Carderera, Cyrille W. Combettes, Hamed Hassani, Amin
Karbasi, Aryan Mokhtari and Sebastian Pokutta [@braun2025conditional]. It formalizes results from
Chapters 1 and 2; numbers refer to the arXiv version [@braun2022conditional].
:::

The Frank–Wolfe algorithm converges at the rate $O(1/t)$ for smooth convex objectives, and this
is optimal in general. The first two chapters of the book *Conditional Gradient Methods*
[@braun2025conditional] collect the tools that give faster rates under additional structure:
inequalities relating smoothness, gaps and strong convexity, a scaling condition at interior
minimizers, and lemmas that turn per-step contractions into rates. This entry formalizes them in
real normed spaces, with the derivative as a continuous linear functional; the objects (the
oracle, the iterates, the step-size rules) are those of
[Frank–Wolfe: the core](../frank-wolfe-core/index.md). The numbering is that of the arXiv version.

:::{admonition} Errata
:class: warning

The formal statements correct three slips in the book:

- **Lemma 2.21.** The first bound $h_t \le c_0(1-c_1)^{t-1}$ is stated for $1 \le t \le t_0$. It
  holds for $t < t_0$ and can fail at $t = t_0$; an exact counterexample is given below.
- **Theorem 2.6.** With the allowed oracle error $2LD^2\delta/(t+3)$ the proof gives the rate
  $2LD^2(1 + 2\delta)/(t+3)$. The stated rate $2LD^2(1 + \delta)/(t+3)$ holds for the error
  $LD^2\delta/(t+3)$.
- **Theorem 2.17.** The statement omits convexity, which the proof uses through Proposition 2.16.
  The contraction factor $1 - r^2/(2Lc^2D^2)$ has to be clipped at $0$: for a constant function
  every $c > 0$ is admissible, and for small $c$ the unclipped bound is negative at odd $t$.
:::

## Smoothness

A function is $L$-smooth when it satisfies the quadratic upper bound
$f(y) \le f(x) + f'(x)(y - x) + \frac{L}{2}\|y - x\|^2$. The core assumes the stronger-looking
condition that $f'$ is $L$-Lipschitz; for convex functions the two agree.

```{prf:lemma} Smoothness and Lipschitz gradients
:label: lem-conditional-gradient-basics-smooth
:enumerator: 1.7

For a convex differentiable $f$ on a real normed space, the quadratic upper bound holds for all
$x, y$ if and only if $f'$ is $L$-Lipschitz in the dual norm.
```

The book states the lemma on a full-dimensional convex domain; here the domain is the whole space.
The converse direction goes through co-coercivity,
$\|f'(y) - f'(x)\|^2 \le 2L(f(y) - f(x) - f'(x)(y - x))$, which needs only the quadratic upper bound
and convexity.

## The Frank–Wolfe gap and the primal gap

The Frank–Wolfe gap $g(x) = \max_{v \in C} f'(x)(x - v)$ is computable and bounds the primal gap
$h(x) = f(x) - \min_C f$ for convex $f$. Conversely, smoothness bounds the Frank–Wolfe gap by the
primal gap, without convexity.

```{prf:proposition} The Frank–Wolfe gap from the primal gap
:label: prop-conditional-gradient-basics-gap
:enumerator: 1.12

Let $f$ be $L$-smooth, not necessarily convex, and let $C$ be convex and bounded with diameter
$D$. For $x \in C$, $g(x) \le h(x) + LD^2/2$ if $h(x) \ge LD^2/2$, and $g(x) \le D\sqrt{2L h(x)}$
if $h(x) \le LD^2/2$.
```

## Approximate linear minimization

The oracle need not be exact: an error that shrinks like the step size costs only a constant
factor in the rate.

```{prf:theorem} Approximate linear minimization
:label: thm-conditional-gradient-basics-approx
:enumerator: 2.6

Let $C$ be compact and convex with diameter $D$, let $f$ be convex and $L$-smooth, and let
$\delta \ge 0$. Suppose every atom satisfies
$f'(x_t)(v_t) \le \min_{v \in C} f'(x_t)(v) + LD^2\delta/(t+3)$ and every step $\gamma_t \in [0, 1]$
does at least as well as every $s \in [0, 1]$ in the smoothness bound, as clipped short steps and
exact line search do. Then $f(x_t) - f(x^*) \le 2LD^2(1 + \delta)/(t+3)$ for $t \ge 1$.
```

The book allows the error $2LD^2\delta/(t+3)$ and states the same rate. With that error, its
proof gives $1 + 2\delta$ instead of $1 + \delta$: the step $2/(t+3)$ times the error is
$(2/(t+3))^2 LD^2\delta$, not half of it. The formal statement uses half the error, as in the
original normalization of @jaggi2013revisiting. The book's bound on the running minimum of the
Frank–Wolfe gaps under approximation is not formalized here.

## Strong convexity and gradient domination

```{prf:lemma} Primal gap bound via strong convexity
:label: lem-conditional-gradient-basics-strong
:enumerator: 2.13

Let $f$ be $\mu$-strongly convex on a convex set $C$, with $\mu > 0$, and let $x^*$ minimize $f$ on
$C$. Then for every $x \in C$,
$f(x) - f(x^*) \le \dfrac{f'(x)(x - x^*)^2}{2\mu\|x - x^*\|^2} \le \dfrac{\|f'(x)\|^2}{2\mu}$.
```

The second inequality says that $f$ is *gradient dominated* with constant $c = 1/\sqrt{2\mu}$:
$f(x) - f(x^*) \le c^2 \|f'(x)\|^2$. A large primal gap forces a large gradient, and this is what
linear convergence needs.

## Interior minimizers

If the minimizer is deep inside $C$, the atom returned by the oracle points far along the negative
gradient.

```{prf:proposition} Scaling condition for an interior minimizer
:label: prop-conditional-gradient-basics-scaling
:enumerator: 2.16

Let $f$ be convex and differentiable, let $x^*$ minimize $f$ on $C$, and let the closed ball of
radius $r > 0$ around $x^*$ lie in $C$. For every $x \in C$ and every minimizer $v$ of $f'(x)$ on
$C$, $f'(x)(x - v) \ge r\|f'(x)\| \ge r\, f'(x)(x - x^*)/\|x - x^*\|$.
```

```{prf:theorem} Linear convergence for an interior minimizer
:label: thm-conditional-gradient-basics-linear
:enumerator: 2.17

Let $C$ be compact and convex with diameter $D$, let $f$ be convex and $L$-smooth, let $x^*$
minimize $f$ on $C$ with the closed ball of radius $r > 0$ around $x^*$ in $C$, and let
$f(x) - f(x^*) \le c^2\|f'(x)\|^2$ on $C$. With short steps or exact line search, from any start
in $C$, $f(x_t) - f(x^*) \le q^t\, LD^2/2$ for all $t \ge 0$, where
$q = \max\{1 - r^2/(2Lc^2D^2), 0\}$.
```

Three details differ from the book:

- **Convexity.** The book states the theorem for smooth gradient dominated $f$. Its proof applies
  Proposition 2.16, which uses convexity, so the formal statement assumes it.
- **The factor $q$.** It is clipped at $0$. If $f$ is constant, every $c$ works, and for small $c$
  the factor $1 - r^2/(2Lc^2D^2)$ is negative, so the unclipped bound fails for odd $t$.
- **The start.** The gradient vanishes at an interior minimizer, so already $f(x_0) - f(x^*) \le
  LD^2/2$ and the bound holds from $t = 0$; the book has the exponent $t - 1$.

The widget runs Frank–Wolfe on $f(x) = \frac12 (x - c)^\top Q (x - c)$ with
$Q = \operatorname{diag}(1, \mu)$, so $L = 1$ and $c^2 = 1/(2\mu)$ in Theorem 2.17. On the
semi-log chart a linear rate is a straight line; the dashed line is the guarantee
$q^t LD^2/2$, drawn while the minimizer is interior. Drag $c$.

```{anywidget} ./widgets/lin.mjs
:css: ./widgets/lin.css
{"region": "square", "objective": "elongated", "cx": 0.45, "cy": 0.25}
```

Things to try:

- **Move $c$ toward an edge.** The inscribed ball shrinks, $q$ approaches $1$, and the guarantee
  flattens. The iterates still converge linearly, but more slowly.
- **Move $c$ outside the square or the triangle.** The minimizer moves to the boundary and the
  short step slows down to a sublinear rate: the iterates zig-zag toward a face.
- **The disk.** With $c$ outside, the minimizer is on the boundary of a strongly convex set and
  the gradient does not vanish there; convergence stays fast, for the reason explained in
  [Frank–Wolfe beyond 1/t under local dual sharpness](../frank-wolfe-local-dual-sharpness/index.md).
- **The open-loop rule** $2/(t+2)$ never converges linearly: its steps shrink no matter how good
  the geometry is.

## From contractions to rates

Most rates for Frank–Wolfe variants come from a per-step inequality for the primal gap. The book's
lemmas turn the basic shapes into rates.

```{prf:lemma} Contractions of mixed type
:label: lem-conditional-gradient-basics-contraction-mixed
:enumerator: 2.21

Let $h_t > 0$, $c_0, c_2, \alpha > 0$, $0 < c_1 < 1$, $h_1 \le c_0$ and
$h_t - h_{t+1} \ge h_t \min\{c_1, c_2 h_t^\alpha\}$ for $t \ge 1$. With $\tau = (c_1/c_2)^{1/\alpha}$ and
$t_0 = \max\{\lfloor \log_{1-c_1}(\tau/c_0) \rfloor + 2, 1\}$, $h_t \le c_0 (1 - c_1)^{t-1}$ for
$1 \le t < t_0$, and $h_t \le \tau/(1 + c_1 \alpha (t - t_0))^{1/\alpha}$ for $t \ge t_0$.
```

While $h_t \ge \tau$ the contraction is linear; once $h_t$ falls below $\tau$ it stays there, the
minimum is $c_2 h_t^\alpha$, and Lemma 2.23 applies from $t_0$ on. The book states the first bound
for $1 \le t \le t_0$. At $t = t_0$ it can fail: for $c_0 = 10$, $c_1 = c_2 = 0.9$ and $\alpha = 1$
we have $\tau = 1$ and $t_0 = 3$, and $h = (10, 5/9, 5/18, \dots)$ satisfies the hypotheses
while $h_3 = 5/18 > c_0 (1 - c_1)^2 = 1/10$. The second bound holds at $t_0$.

```{prf:lemma} Linear contraction
:label: lem-conditional-gradient-basics-contraction-linear
:enumerator: 2.22

If $h_t \ge 0$, $0 < c_1 < 1$, $h_1 \le c_0$ and $h_t - h_{t+1} \ge c_1 h_t$ for $t \ge 1$, then
$h_t \le c_0 (1 - c_1)^{t-1}$ for $t \ge 1$.
```

```{prf:lemma} Power contraction
:label: lem-conditional-gradient-basics-contraction-power
:enumerator: 2.23

If $h_t > 0$, $c_0, c_2, \alpha > 0$, $h_1 \le c_0$ and $h_t - h_{t+1} \ge c_2 h_t^{1+\alpha}$ for
$t \ge 1$, then $h_t \le c_0 / (1 + c_2 c_0^\alpha \alpha (t - 1))^{1/\alpha}$ for $t \ge 1$.
```

The proof of the power case shows that $h_t^{-\alpha}$ grows by at least $\alpha c_2$ per step,
using $s^{-\alpha} \ge 1 + \alpha(1 - s)$ for $0 < s \le 1$.

## Not yet covered

The lower bounds of Section 2.1.2 are not formalized here. The away-step, fully-corrective and
pairwise variants of Sections 2.2.5, 2.2.6 and 3.1.1 are in
[Conditional gradient methods: away-step, fully-corrective and pairwise Frank–Wolfe](../away-step-frank-wolfe/index.md). Rates over uniformly convex sets are in
[Frank–Wolfe beyond 1/t under local dual sharpness](../frank-wolfe-local-dual-sharpness/index.md),
and the baseline results of Chapter 2 are in
[The Frank–Wolfe algorithm: a short introduction](../frank-wolfe-introduction/index.md).

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/CGBasics/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/conditional-gradient-basics.md
```
