---
title: "Blended pairwise conditional gradients: BPCG and LazyBPCG"
numbering:
  headings: false
---

```{include} ../_generated/provenance/blended-pairwise-conditional-gradients.md
```

:::{note}
This entry formalizes the paper *Sparser Kernel Herding with Pairwise Conditional Gradients without
Swap Steps* by Kazuma Tsuji, Ken'ichiro Tanaka and Sebastian Pokutta [@tsuji2021sparser], without
its application to kernel herding; numbers refer to the arXiv version.
:::

Pairwise Frank–Wolfe moves weight from the away vertex to the Frank–Wolfe vertex. When the
Frank–Wolfe vertex is new and the away vertex loses all its weight, the step is a swap step: the
active set keeps its size and the step need not make much progress, and the known bounds on runs of
swap steps involve $|V|!$ (see
[Conditional gradient methods: away-step, fully-corrective and pairwise Frank–Wolfe](../away-step-frank-wolfe/index.md)).
Blended pairwise conditional gradients avoid swap steps altogether: pairwise steps stay inside the
active set, and new vertices enter only through Frank–Wolfe steps. The objects are those of
[Frank–Wolfe: the core](../frank-wolfe-core/index.md), on a polytope $P = \operatorname{conv} V$ with
$V$ a finite set in a real normed space.

## The algorithm

```{prf:definition} BPCG step
:label: def-blended-pairwise-conditional-gradients-step
:nonumber:

At $x$ with active set $S$ and weights $\lambda$, let $a$ and $s$ maximize and minimize $f'(x)$ over
$S$, and let $w$ minimize $f'(x)$ over $V$. If $f'(x)(a - s) \ge f'(x)(x - w)$, the step moves weight
$\gamma \in [0, \lambda_a]$ from $a$ to $s$, with exact line search, and drops $a$ when its weight is
used up; otherwise it is a Frank–Wolfe step toward $w$ with exact line search on $[0, 1]$.
```

```{prf:definition} BPCG run
:label: def-blended-pairwise-conditional-gradients-run
:nonumber:

A run starts at a vertex $x_0$ with active set $\{x_0\}$ and weight $1$, and every step is a BPCG
step (Algorithm 1), for any choice of the vertices among the optimal ones.
```

## Convergence

```{prf:theorem} Convex objectives
:label: thm-blended-pairwise-conditional-gradients-convex
:enumerator: 3.1

Let $f$ be convex and $L$-smooth and let $D$ be the diameter of $V$. Every BPCG run satisfies
$f(x_T) - f(x^*) \le 4LD^2/T$ for $T \ge 1$.
```

```{prf:theorem} Strongly convex objectives over polytopes
:label: thm-blended-pairwise-conditional-gradients-linear
:enumerator: 3.2

If moreover $f$ is $\mu$-strongly convex on $P$ and $\delta > 0$ has the scaling property of the
pyramidal width, every BPCG run satisfies
$f(x_T) - f(x^*) \le (f(x_0) - f(x^*)) \exp(-cT)$ with
$c = \frac{1}{2}\min\{1/2, \mu\delta^2/(4LD^2)\}$.
```

The chosen direction has gap $G = \max\{f'(x)(a - s), f'(x)(x - w)\}$. It is at least the
Frank–Wolfe gap, hence at least the primal gap, and at least half of $f'(x)(a - w)$, because
$f'(x)(a - x) \le f'(x)(a - s)$. A step that does not drop a vertex gains at least
$\min\{G/2, G^2/(2LD^2)\}$; for a pairwise step whose line search ends inside $[0, \lambda_a]$ this
uses that, by convexity, the step is optimal along the whole ray. With geometric strong
convexity, $f(x) - f(x^*) \le f'(x)(a - w)^2/(2\mu\delta^2)$, every such step contracts the primal
gap by $1 - \min\{1/2, \mu\delta^2/(4LD^2)\}$. Only Frank–Wolfe steps add vertices and only drop steps
remove them, so drop steps are at most as many as the other steps, and at least half of all steps
make progress.

:::{note}
**Differences from the paper.** A pairwise step whose away vertex is also the local Frank–Wolfe
vertex does not drop it: the step is then zero, and dropping a vertex that keeps its weight would
make the active set inconsistent. Theorem 3.2 is stated for any constant $\delta > 0$ with the
scaling property, in particular the pyramidal width.
:::

## Lazified BPCG

The lazified variant (Algorithm 2 of the paper) calls the linear minimization oracle only when the
active set offers too little: with a gap estimate $\Phi_t$ and an accuracy $J \ge 1$, it takes a local
pairwise step if $f'(x_t)(a_t - s_t) \ge \Phi_t$, a Frank–Wolfe step toward the Frank–Wolfe vertex
$w_t$ if $f'(x_t)(x_t - w_t) \ge \Phi_t/J$, and otherwise a gap step that halves $\Phi$.

```{prf:definition} Lazified BPCG step
:label: def-blended-pairwise-conditional-gradients-lazy-step
:nonumber:

If $f'(x)(a - s) \ge \Phi$, the step is the local pairwise step of BPCG and $\Phi$ stays. Otherwise,
with a Frank–Wolfe vertex $w$, it is a Frank–Wolfe step with exact line search if
$f'(x)(x - w) \ge \Phi/J$, and $\Phi$ stays; if not, the iterate stays and $\Phi$ is halved.
```

```{prf:theorem} Lazified BPCG, convex objectives
:label: thm-blended-pairwise-conditional-gradients-lazy
:enumerator: 3.6

Let $f$ be convex and $L$-smooth, $J \ge 1$ and $h_0/2 \le \Phi_0 \le LD^2/2$. Every run of lazified
BPCG has primal gap at most $\varepsilon > 0$ after
$\lceil \log_2(\Phi_0/\varepsilon) \rceil_+ + 1 + 2\lceil 8J^2LD^2/\varepsilon \rceil$ iterations.
```

A gap step certifies $h_t \le f'(x_t)(x_t - w_t) < \Phi_t/J \le \Phi_t$, so $\Phi_t \ge h_t/2$
throughout. A local pairwise step that does not drop a vertex gains at least $\Phi_t^2/(2LD^2)$ and a
Frank–Wolfe step at least $\Phi_t^2/(2J^2LD^2)$; drop steps are at most as many as Frank–Wolfe steps.
The paper states case (B) as $\mathcal{O}(1/T)$; the formal statement gives explicit constants.

## Not yet covered

Case (A) of Theorem 3.6, linear convergence of lazified BPCG for strongly convex objectives over
polytopes, is not formalized here yet; the application to kernel herding is out of scope.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/BPCG/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/blended-pairwise-conditional-gradients.md
```
