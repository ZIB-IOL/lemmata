---
title: "Conditional gradient methods: AdaFW, LazyFW, LazyAFW, NEP-FW and BCG"
numbering:
  headings: false
---

```{include} ../_generated/provenance/conditional-gradient-improvements.md
```

:::{note}
This entry comes from the book *Conditional Gradient Methods: From Core Principles to AI
Applications* by Gábor Braun, Alejandro Carderera, Cyrille W. Combettes, Hamed Hassani, Amin
Karbasi, Aryan Mokhtari and Sebastian Pokutta [@braun2025conditional]. It formalizes results from
Sections 3.1.2, 3.1.3, 3.1.5, 3.1.6 and 3.2.2; numbers refer to the arXiv
version [@braun2022conditional].
:::

:::{admonition} Errata
:class: warning

The formal statements correct four slips in the book:

- **Algorithm 3.8.** The directions $d_t$ have the wrong sign: with $d_t = x_t - v_t$ for away
  steps and $d_t = v_t - x_t$ for Frank–Wolfe steps, $\langle \nabla f(x_t), d_t\rangle < 0$, so the
  step $\gamma_t$ is negative and the clipping at $\gamma_{\max}$ never applies. The formal run moves
  away from the away vertex and toward the Frank–Wolfe vertex with nonnegative short steps.
- **Theorem 3.16, positive answers before the first negative one.** The proof sketch obtains the
  linear contraction from $2\phi_t \ge \sqrt{2\mu\delta^2 h_t}$, which a negative answer
  certifies; before the first negative answer only a constant progress $\phi_0^2/(2K^2LD^2)$ per step
  is available, and these steps are not counted. The formal count adds $2\lceil 4K^2LD^2/\phi_0\rceil$.
- **Theorem 3.16, the constant.** At a negative answer $2\phi_t \ge \sqrt{2\mu\delta^2 h_t}$, but
  $\phi$ is halved right after, so the following steps only have $4\phi_t \ge \sqrt{2\mu\delta^2 h_t}$.
  The contraction factor is then $1 - \mu\delta^2/(16K^2LD^2)$, and the count has
  $16K^2LD^2/(\mu\delta^2)$ in place of $4K^2LD^2/(\mu\delta^2)$.
- **Corollary 3.33, the constant.** The step chosen by away-step Frank–Wolfe has gap at least half
  of $f'(x)(a - v)$, so geometric sharpness (Lemma 3.32) gives the contraction factor
  $1 - \min\{1/2, \delta^2/(8c^2LD^2)\}$ for $\theta = 1/2$, not $1 - \delta^2/(2c^2LD^2)$; for
  $\theta < 1/2$ the same factor $4$ appears inside $(c^2LD^2/\delta^2)^{1/(1-2\theta)}$. The formal
  statement uses the constant of the proof.
:::

Chapter 3 of the book improves the Frank–Wolfe algorithm in several directions: step sizes that
adapt to unknown smoothness, cheaper oracles, and faster rates under additional structure. This
entry collects these variants; the objects are those of
[Frank–Wolfe: the core](../frank-wolfe-core/index.md), and the rates build on
[Conditional gradient methods: smoothness, scaling and linear rates](../conditional-gradient-basics/index.md).
The pairwise variant of Section 3.1.1 is in
[Conditional gradient methods: away-step, fully-corrective and pairwise Frank–Wolfe](../away-step-frank-wolfe/index.md).

## Adaptive step sizes (AdaFW)

The short step needs the smoothness constant $L$, which is often unknown or pessimistic. The
adaptive strategy of @pedregosa2018linearly keeps an estimate $M$, takes the short step for $M$
and checks that it decreases $f$ as the smoothness bound for $M$ predicts; if not, it multiplies
$M$ by $\tau > 1$ and tries again (Algorithm 3.4). Algorithm 3.5 (AdaFW) is vanilla Frank–Wolfe
with these steps.

```{prf:definition} Short step for an estimate
:label: def-conditional-gradient-improvements-ada-step
:nonumber:

For an estimate $M > 0$, the short step from $x$ toward $v$ is
$\gamma = \min\{f'(x)(x - v)/(M\|x - v\|^2), 1\}$.
```

```{prf:definition} Sufficient decrease test
:label: def-conditional-gradient-improvements-sufficient-decrease
:nonumber:

The estimate $M$ passes the test at $x$ toward $v$ if the short step $\gamma$ for $M$ satisfies
$f(x + \gamma(v - x)) - f(x) \le \gamma f'(x)(v - x) + \gamma^2 M\|x - v\|^2/2$.
```

```{prf:lemma} Smoothness passes the test
:label: lem-conditional-gradient-improvements-smooth-test
:nonumber:

If $f$ is $L$-smooth and $M \ge L$, the estimate $M$ passes the test at every $x$ toward every $v$.
```

```{prf:proposition} The search terminates
:label: prop-conditional-gradient-improvements-terminates
:nonumber:

Let $f$ be $L$-smooth, $M_0 > 0$ and $\tau > 1$. There is a first $k$ for which $M_0\tau^k$
passes the test; it satisfies $k \le \lceil \log_\tau (L/M_0) \rceil$, and
$M_0\tau^k \le \max\{M_0, \tau L\}$.
```

```{prf:theorem} AdaFW keeps the rates of vanilla Frank–Wolfe
:label: thm-conditional-gradient-improvements-adafw
:nonumber:

Let $C$ be compact and convex with diameter $D$, and let $f$ be convex and $L$-smooth with
$L \le K$. If every step of a Frank–Wolfe run with exact linear minimization is the short step
for an estimate $0 < M_t \le K$ that passes the test, then for $t \ge 1$
$f(x_t) - f(x^*) \le 2KD^2/(t+3)$ and $\min_{0 \le \tau \le t} g_\tau \le 4KD^2/(t+3)$.
```

The short step for $M$ minimizes $-s g + s^2 M \|x - v\|^2/2$ over $s \in [0, 1]$, so a step that
passes the test does at least as well as every $s \in [0, 1]$ in the smoothness bound for $K$,
and Theorem 2.2 of the book applies with $K$ in place of $L$. By the proposition, $K = \max\{M_0,
\tau L\}$ works when every search starts at most at $M_0$. A different adaptive rule, which tests
the sign of $f'$ at the new point instead of function values, is analyzed in
[The Frank–Wolfe algorithm: a short introduction](../frank-wolfe-introduction/index.md)
(Lemmas 4.10 and 4.11).

## Lazification (LazyFW and LazyAFW)

A linear minimization oracle solves a linear program exactly in every iteration, although an
improving vertex is all the algorithm needs. The weak separation oracle of @braun2016lazifying
receives a target $\phi$ and an accuracy $K \ge 1$; it either returns a vertex $v$ that improves on
the current iterate by more than $\phi/K$, or certifies that no point improves by more than $\phi$.
The parameter-free lazy conditional gradient algorithm (Algorithm 3.7) halves $\phi$ after every
negative answer.

```{prf:definition} Lazy conditional gradient run
:label: def-conditional-gradient-improvements-lcg-run
:nonumber:

In every iteration, either the oracle returns $v \in C$ with $f'(x_t)(x_t - v) > \phi_t/K$ and the
step toward $v$ does at least as well as every $s \in [0, 1]$ in the smoothness bound, with
$\phi_{t+1} = \phi_t$, or it certifies $f'(x_t)(x_t - z) \le \phi_t$ for all $z \in C$, and then
$x_{t+1} = x_t$ and $\phi_{t+1} = \phi_t/2$.
```

```{prf:theorem} Lazy conditional gradients
:label: thm-conditional-gradient-improvements-lazy
:enumerator: 3.15

Let $C$ be compact and convex with diameter $D$, let $f$ be convex and $L$-smooth, $K \ge 1$ and
$h_0/2 \le \phi_0 \le LD^2/2$. Every run has primal gap at most $\varepsilon > 0$ after
$\lceil \log_2(\phi_0/\varepsilon) \rceil_+ + \lceil 8K^2LD^2/\varepsilon \rceil$ iterations.
```

A negative answer certifies $h_t \le \phi_t$, so $\phi_t \ge h_t/2$ throughout. A positive answer
gains at least $\phi_t^2/(2K^2LD^2) \ge h_t^2/(8K^2LD^2)$, so after $k$ positive answers
$h_t \le 8K^2LD^2/(k+8)$; after $\lceil \log_2(\phi_0/\varepsilon) \rceil_+ + 1$ negative
answers, the last one certifies $h_t \le \phi_t \le \varepsilon$.

### Lazy away-step Frank–Wolfe (LazyAFW)

Algorithm 3.8 makes both searches of away-step Frank–Wolfe lazy: the weak separation oracle looks
for an away vertex in the active set or a Frank–Wolfe vertex in $V$, each improving by more than
$\phi_t/K$, and halves $\phi$ when neither exists.

```{prf:definition} Lazy away-step Frank–Wolfe run
:label: def-conditional-gradient-improvements-lazy-afw-run
:nonumber:

A run starts at a vertex with active set $\{x_0\}$ and weight $1$. In every iteration the oracle
returns $a \in S_t$ with $f'(x_t)(a - x_t) > \phi_t/K$, followed by an away step with the short step
clipped at $\lambda_a/(1 - \lambda_a)$, or $v \in V$ with $f'(x_t)(x_t - v) > \phi_t/K$, followed by a
Frank–Wolfe step with the short step clipped at $1$; or it certifies that no vertex of $S_t$ or $V$
improves by more than $\phi_t$, and then $\phi$ is halved.
```

```{prf:theorem} Lazy away-step Frank–Wolfe
:label: thm-conditional-gradient-improvements-lazy-afw
:enumerator: 3.16

Let $f$ be convex, $L$-smooth and $\mu$-strongly convex on $P = \operatorname{conv} V$, let
$\delta > 0$ have the scaling property of the pyramidal width, $K \ge 1$ and
$h_0/2 \le \phi_0 \le LD^2/2$. Every run has primal gap at most $\varepsilon > 0$ after
$\lceil \log_2(\phi_0/\varepsilon) \rceil_+ + 1 + 2\lceil 4K^2LD^2/\phi_0 \rceil +
2\lceil (16K^2LD^2/(\mu\delta^2)) \ln(h_0/\varepsilon) \rceil_+$ iterations.
```

A negative answer certifies $h_t \le \phi_t$ and, by geometric strong convexity,
$\mu\delta^2 h_t \le 2\phi_t^2$; after the halving, $\mu\delta^2 h_t \le 8\phi_t^2$ for the following
steps. Steps that do not drop a vertex gain at least $\phi_t^2/(2K^2LD^2)$, which before the first
negative answer is the constant $\phi_0^2/(2K^2LD^2)$ and after it at least
$\mu\delta^2 h_t/(16K^2LD^2)$. Drop steps are at most as many as the other positive steps.

## Sharpness

Strong convexity bounds the distance to the minimizer by the square root of the primal gap.
Sharpness, also called the Hölder error bound, relaxes the exponent $1/2$ to any $\theta \in (0, 1]$
and allows a set of minimizers $\Omega^*$.

```{prf:definition} Sharpness
:label: def-conditional-gradient-improvements-sharp
:enumerator: 3.25

A function $f$ is $(c, \theta)$-sharp over $C$ if
$\operatorname{dist}(x, \Omega^*) \le c\,(f(x) - f(x^*))^\theta$ for all $x \in C$ and all minimizers
$x^*$ of $f$ over $C$.
```

```{prf:lemma} Primal gap bound from sharpness
:label: lem-conditional-gradient-improvements-sharp-gap
:enumerator: 3.31

Let $C$ be compact and $f$ convex, differentiable and $(c, \theta)$-sharp over $C$. For every $x \in C$
with positive primal gap $h$ there is a minimizer $y$ with
$h^{1-\theta}/c \le f'(x)(x - y)/\|x - y\|$.
```

```{prf:lemma} Geometric sharpness
:label: lem-conditional-gradient-improvements-geometric-sharpness
:enumerator: 3.32

Let $f$ be convex, differentiable and $(c, \theta)$-sharp over $P = \operatorname{conv} V$, and let
$\delta > 0$ have the scaling property of the pyramidal width. If $x \in \operatorname{conv} S$ with
$S \subseteq V$, $a$ is an away vertex of $S$, $v$ a Frank–Wolfe vertex and the primal gap $h$ at $x$
is positive, then $h^{1-\theta}/c \le f'(x)(a - v)/\delta$.
```

The nearest minimizer $y$ exists because the set of minimizers is compact; sharpness bounds
$\|x - y\|$ by $c\,h^\theta$ and convexity gives $h \le f'(x)(x - y)$. The scaling property then
replaces $f'(x)(x - y)/\|x - y\|$ by $f'(x)(a - v)/\delta$.

```{prf:corollary} Away-step Frank–Wolfe under sharpness, $\theta = 1/2$
:label: cor-conditional-gradient-improvements-sharp-afw
:enumerator: 3.33

Let $f$ be convex, $L$-smooth and $(c, 1/2)$-sharp over $P = \operatorname{conv} V$, and let
$\delta > 0$ have the scaling property of the pyramidal width. Every run of away-step Frank–Wolfe
satisfies $f(x_t) - f(x^*) \le (1 - \min\{1/2, \delta^2/(8c^2LD^2)\})^{\lfloor (t-1)/2 \rfloor}
LD^2/2$ for $t \ge 1$.
```

A step of away-step Frank–Wolfe that does not drop a vertex gains at least
$\min\{h/2, f'(x)(a - v)^2/(8LD^2)\}$, and Lemma 3.32 bounds $f'(x)(a - v)^2$ below by
$\delta^2 h/c^2$. As in Theorem 2.29, the exponent is $\lfloor (t-1)/2 \rfloor$ instead of the book's
$\lceil (t-1)/2 \rceil$.

:::{note}
**Differences from the book.** Lemmas 3.31 and 3.32 are stated for points with positive primal
gap. At a minimizer the left-hand side is $0^{1-\theta}/c$, which is $1/c$ for $\theta = 1$, while the
right-hand side is not defined.
:::

## The nearest extreme point oracle (NEP-FW)

When the minimizers lie on a low-dimensional face, the Frank–Wolfe vertices keep jumping across
the polytope. The nearest extreme point oracle of @garber2021frank adds a proximity term: it
minimizes $f'(x_t)(v) + L\gamma_t\|x_t - v\|^2/2$ over the vertices, which in the Euclidean norm
keeps the steps short when the iterates are close to the optimal face.

```{prf:definition} NEP-FW run
:label: def-conditional-gradient-improvements-nep-run
:nonumber:

In a real inner product space, a run starts at a vertex; with $\gamma_t = 2/(t+2)$, the vertex
$v_t \in V$ minimizes $f'(x_t)(v) + L\gamma_t\|x_t - v\|^2/2$ over $V$, and
$x_{t+1} = x_t + \gamma_t(v_t - x_t)$ (Algorithm 3.12).
```

```{prf:theorem} Frank–Wolfe with the nearest extreme point oracle
:label: thm-conditional-gradient-improvements-nep
:enumerator: 3.36

Let $f$ be convex, $L$-smooth and $(c, \theta)$-sharp over $P = \operatorname{conv} V$ with
$0 < \theta \le 1/2$, and let $S^* \subseteq V$ be a set of vertices whose convex hull contains all
minimizers; let $D$ and $D_0$ be the diameters of $V$ and $S^*$. For $t \ge 1$,

$$
f(x_t) - f(x^*) \le \frac{LD^2}{t(t+1)} + \frac{2LD_0^2}{t+2} +
\frac{2^{2\theta+1} L^{2\theta+1} c^2 D^{4\theta}}{t(t+1)} \cdot
\begin{cases} \frac{(t+2)^{1-2\theta}}{1-2\theta} & \theta < 1/2, \\ \ln(t+2) & \theta = 1/2. \end{cases}
$$
```

The oracle's vertex is at least as good as any convex combination of vertices in the smoothness
bound. Against a representation of the minimizer, this gives
$h_{t+1} \le (1 - \gamma_t)h_t + \gamma_t^2 LD^2/2$, hence $h_t \le 2LD^2/(t+2)$; against a
representation of the nearest minimizer $y$ over $S^*$, the identity
$\sum_u \lambda_u\|u - x\|^2 = \|y - x\|^2 + \sum_u \lambda_u\|u - y\|^2$ gives
$h_{t+1} \le (1 - \gamma_t)h_t + \gamma_t^2 L(\operatorname{dist}(x_t, \Omega^*)^2 + D_0^2)/2$
(Lemma 3.37). Sharpness bounds the distance by $c\,h_t^\theta$, and summing the recursion with weights
$t(t+1)$ gives the theorem.

## Blended conditional gradients (BCG)

Blended conditional gradients [@braun2018blended] avoid calling the linear minimization oracle as
long as the active set offers enough progress: if the away vertex and the local Frank–Wolfe vertex of
the active set differ by at least $\phi_t$ in $f'(x_t)$, a simplex descent step (Oracle 3.43)
optimizes over the active set; otherwise the weak separation oracle provides a Frank–Wolfe step or
halves $\phi$ (Algorithm 3.44).

```{prf:definition} BCG run
:label: def-conditional-gradient-improvements-bcg-run
:nonumber:

Every iterate lies in the convex hull of its active set $S_t \subseteq V$. If $f'(x_t)(a - s) \ge \phi_t$
for some $a, s \in S_t$, the simplex descent oracle returns $x_{t+1} \in \operatorname{conv} S_{t+1}$
with $S_{t+1} \subseteq S_t$, and either drops a vertex without increasing $f$ or decreases $f$ by at
least $\max_{u, w \in S_t} f'(x_t)(u - w)^2/(L_S |S_t|)$. Otherwise the weak separation oracle
returns a vertex improving by more than $\phi_t/K$, followed by a Frank–Wolfe step, or certifies that
none improves by more than $\phi_t$, and $\phi$ is halved.
```

```{prf:theorem} Blended conditional gradients
:label: thm-conditional-gradient-improvements-bcg
:enumerator: 3.42

Let $f$ be convex and $L$-smooth on $P = \operatorname{conv} V$ with diameter $D$, $K \ge 1$,
$h_0/2 \le \phi_0 \le LD^2/2$, and let all active sets have at most $k$ vertices. With
$Q = \max\{8K^2LD^2, 4L_S k\}$, every run has primal gap at most $\varepsilon > 0$ after
$\lceil \log_2(\phi_0/\varepsilon) \rceil_+ + 1 + 2\lceil Q/\varepsilon \rceil$ iterations.
```

As for lazy conditional gradients, $\phi_t \ge h_t/2$ throughout. A simplex descent step gains at
least $\phi_t^2/(L_S k)$ and a Frank–Wolfe step at least $\phi_t^2/(2K^2LD^2)$, so every step that does
not drop a vertex gains at least $h_t^2/Q$, and drop steps are at most as many as Frank–Wolfe steps.

```{prf:theorem} Blended conditional gradients, strongly convex objectives
:label: thm-conditional-gradient-improvements-bcg-linear
:enumerator: 3.42

If moreover $f$ is $\mu$-strongly convex on $P$ and $\delta > 0$ has the scaling property of the
pyramidal width, every run has primal gap at most $\varepsilon > 0$ after
$\lceil \log_2(\phi_0/\varepsilon) \rceil_+ + 1 + 2\lceil Q/(2\phi_0) \rceil +
2\lceil (2Q/(\mu\delta^2)) \ln(h_0/\varepsilon) \rceil_+$ iterations.
```

At a negative answer of the weak separation oracle the simplex descent criterion failed as well, so
$f'(x_t)(a - w) < 2\phi_t$ for the away vertex $a$ and the Frank–Wolfe vertex $w$, and geometric
strong convexity gives $\mu\delta^2 h_t \le 2\phi_t^2$; after $\phi$ is halved,
$\mu\delta^2 h_t \le 8\phi_t^2$, and the steps that do not drop a vertex contract the primal gap by
$1 - \mu\delta^2/(2Q)$.

:::{note}
**Differences from the book.** Theorem 3.42 is stated in the book as
$\mathcal{O}(LD^2 \dim P/\varepsilon)$, without proof; the formal statement gives explicit constants,
with the bound $k$ on the active sets in place of $\mathcal{O}(\dim P)$. The constant $L_S$ of the
simplex descent oracle is the smoothness constant in the weights of the active set, of order
$LD^2$ for the simplex descent of Lemma 3.45, which gives the book's $\mathcal{O}(LD^2 k/\varepsilon)$.
Lemma 3.45 is not formalized here.
:::

## Not yet covered

From Section 3.1.5, Corollary 3.33 for $\theta < 1/2$, the comparison with gradient domination
(Lemma 3.35), the Hoffman bound (Lemma 3.27) and the Łojasiewicz-type Lemma 3.30 are not
formalized here; from Section 3.2.2, the simplex descent step of Lemma 3.45.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/CGImprovements/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/conditional-gradient-improvements.md
```
