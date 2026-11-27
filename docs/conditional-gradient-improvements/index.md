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
Karbasi, Aryan Mokhtari and Sebastian Pokutta [@braun2025conditional]. It formalizes Section 3.1.2;
numbers refer to the arXiv version [@braun2022conditional].
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

## Not yet covered

Lazification with LazyFW and LazyAFW (Section 3.1.3), sharpness (Section 3.1.5), the nearest
extreme point oracle (NEP-FW, Section 3.1.6) and blended conditional gradients (BCG,
Section 3.2.2) are not formalized here yet.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/CGImprovements/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/conditional-gradient-improvements.md
```
