---
title: "Frank–Wolfe: the core"
numbering:
  headings: false
---

```{include} ../_generated/provenance/frank-wolfe-core.md
```

This entry defines the objects of the Frank–Wolfe algorithm once, for all Frank–Wolfe entries of
the archive: the linear minimization oracle, the Frank–Wolfe step and its iterates, the usual
step-size rules, the Frank–Wolfe gap and the standard assumptions. It also proves the basic facts
that every analysis of the method starts from. Entries import these definitions instead of
restating them. [Frank–Wolfe beyond 1/t under local dual sharpness](../frank-wolfe-local-dual-sharpness/index.md)
is the first entry built on it.

The results are classical [@frank1956algorithm; @levitin1966constrained; @jaggi2013revisiting];
@braun2025conditional is a detailed introduction. The setting is a real normed space, so that
the definitions also cover non-Euclidean norms, and derivatives are continuous linear
functionals. A second, equivalent set of definitions uses inner products and gradients for
Hilbert spaces; the two are related through the Riesz isometry.

## The algorithm

```{prf:definition} Linear minimization oracle
:label: def-frank-wolfe-core-lmo
:nonumber:

Let $C$ be a subset of a real normed space $E$. A *linear minimization oracle* for $C$ is a rule
$\mathrm{lmo}$ that returns, for every continuous linear functional $g$, a point
$\mathrm{lmo}(g) \in \operatorname{argmin}_{y \in C} g(y)$. When there are several minimizers,
the rule selects one of them; any rule is allowed, but it is fixed.
```

```{prf:definition} The Frank–Wolfe algorithm
:label: def-frank-wolfe-core-fw
:nonumber:

For an objective $f$ with derivative $f'$ and a start $x_0 \in C$, Frank–Wolfe takes the atom
$v_t = \mathrm{lmo}(f'(x_t))$ and moves toward it, $x_{t+1} = x_t + \gamma_t (v_t - x_t)$. The step
size is $\gamma_t = \ell/(t + \ell)$ (*open loop*, classically $\ell = 2$), or the *short step*
$\gamma_t = \min\{f'(x_t)(x_t - v_t)/(L\|v_t - x_t\|^2), 1\}$ (and $0$ if $v_t = x_t$), or
*exact line search*, a fixed rule choosing a minimizer of $f$ on the segment.
```

```{prf:definition} Frank–Wolfe gap
:label: def-frank-wolfe-core-gap
:nonumber:

The *Frank–Wolfe gap* of $f$ at $x$ is $\max_{v \in C} f'(x)(x - v)$.
```

```{prf:definition} Smoothness
:label: def-frank-wolfe-core-smooth
:nonumber:

$f$ is *$L$-smooth* if it is differentiable and its derivative is $L$-Lipschitz in the operator
norm: $\|f'(x) - f'(y)\| \le L \|x - y\|$.
```

```{prf:definition} Standing assumptions
:label: def-frank-wolfe-core-setting
:nonumber:

$C$ is compact and convex with linear minimization oracle $\mathrm{lmo}$, and $f$ is convex and
$L$-smooth with $L > 0$.
```

```{prf:definition} Uniformly convex sets
:label: def-frank-wolfe-core-uc
:nonumber:

For $\alpha > 0$ and $q \ge 2$, the set $C$ is *$(\alpha, q)$-uniformly convex* if
$\lambda x + (1-\lambda) y + \lambda (1-\lambda)\, \alpha \|x - y\|^q z \in C$ for all
$x, y \in C$, $\lambda \in [0, 1]$ and unit vectors $z$.
```

In a Hilbert space the oracle may instead answer gradient vectors, and the step uses $\nabla f$;
these are the objects of `HilbertDefs.lean`.

```{prf:definition} The Frank–Wolfe algorithm in a Hilbert space
:label: def-frank-wolfe-core-hilbert-fw
:nonumber:

With an oracle $\mathrm{lmo}$ on vectors, $x_{t+1} = x_t + \gamma_t (\mathrm{lmo}(\nabla f(x_t)) - x_t)$.
It is the algorithm above for the oracle $g \mapsto \mathrm{lmo}(\nabla_g)$, where $\nabla_g$ is
the vector representing $g$.
```

## Basic results

```{prf:lemma} The gap inequalities
:label: lem-frank-wolfe-core-gaps
:nonumber:

Let $C$ be compact, $f$ convex and differentiable, $x^\star$ a minimizer of $f$ on $C$ and
$x \in C$. Then
$f(x) - f(x^\star) \le f'(x)(x - x^\star) \le \max_{v \in C} f'(x)(x - v)$:
the primal gap is at most the dual gap, which is at most the Frank–Wolfe gap.
```

```{prf:lemma} The descent lemma
:label: lem-frank-wolfe-core-descent
:nonumber:

If $f$ is $L$-smooth, then $f(y) \le f(x) + f'(x)(y - x) + \tfrac{L}{2}\|y - x\|^2$ for all
$x, y$.
```

```{prf:lemma} Primal progress
:label: lem-frank-wolfe-core-progress
:nonumber:

If $f$ is $L$-smooth, a step of length $\gamma$ from $x$ toward $v$ satisfies
$f(x + \gamma (v - x)) \le f(x) - \gamma f'(x)(x - v) + \gamma^2 \tfrac{L}{2} \|v - x\|^2$.
```

```{prf:theorem} $O(1/t)$ convergence
:label: thm-frank-wolfe-core-rate
:nonumber:

Under the standing assumptions, with the open-loop rule $\gamma_t = 2/(t+2)$, short steps or
exact line search, $f(x_t) - f(x^\star) \le 2LD^2/(t+2)$ for every $t \ge 1$, where $D$ is the
diameter of $C$.
```

The proof combines the two lemmas. One step toward the atom gives
$h_{t+1} \le (1-\gamma) h_t + \gamma^2 L D^2/2$ for the primal gap $h_t$, by the gap
inequalities and the progress lemma. Short steps and exact line search do at least as well as
$\gamma = 2/(t+2)$, and the recursion with that step gives $2LD^2/(t+2)$.

```{prf:theorem} $O(1/t)$ convergence in a Hilbert space
:label: thm-frank-wolfe-core-rate-hilbert
:nonumber:

The same bound for the algorithm in the language of gradients. It follows from the previous
theorem through the Riesz isometry, since the two algorithms produce the same iterates.
```

## Entries building on the core

- [Frank–Wolfe beyond 1/t under local dual sharpness](../frank-wolfe-local-dual-sharpness/index.md)
  uses the Hilbert-space objects, and its Proposition 2.2 is the theorem above.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FrankWolfe/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-core.md
```
