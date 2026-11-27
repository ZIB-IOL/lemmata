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
Sections 3.1.2, 3.1.3 and 3.1.5; numbers refer to the arXiv version [@braun2022conditional].
:::

:::{admonition} Errata
:class: warning

The formal statements correct three slips in the book:

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

:::{note}
**Differences from the book.** Lemmas 3.31 and 3.32 are stated for points with positive primal
gap. At a minimizer the left-hand side is $0^{1-\theta}/c$, which is $1/c$ for $\theta = 1$, while the
right-hand side is not defined.
:::

## Not yet covered

From Section 3.1.5, the convergence of away-step Frank–Wolfe under sharpness (Corollary 3.33), the
comparison with gradient domination (Lemma 3.35), the Hoffman bound (Lemma 3.27) and the
Łojasiewicz-type Lemma 3.30 are not formalized here yet; nor are the nearest extreme point oracle
(NEP-FW, Section 3.1.6) and blended conditional gradients (BCG, Section 3.2.2).

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/CGImprovements/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/conditional-gradient-improvements.md
```
