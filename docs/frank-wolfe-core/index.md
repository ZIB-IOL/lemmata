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

## Runs, error bounds and strong convexity

Many analyses follow a single run of the algorithm, whatever the oracle answers, and assume
properties of the objective only on the feasible region. Faster rates for structured problems
add a growth condition, typically a Hölderian error bound or strong convexity. The core provides
these objects as well.

```{prf:definition} Frank–Wolfe run
:label: def-frank-wolfe-core-run
:nonumber:

A *Frank–Wolfe run* on $C$ for the derivative $f'$ consists of iterates $x_t$, atoms $v_t$ and
step sizes $\gamma_t$ with $x_0 \in C$, $v_t \in \operatorname{argmin}_{y \in C} f'(x_t)(y)$,
$\gamma_t \in [0, 1]$ and $x_{t+1} = x_t + \gamma_t (v_t - x_t)$. Ties may be broken differently in
every iteration, and the step sizes are arbitrary.
```

```{prf:definition} Smoothness over a set
:label: def-frank-wolfe-core-smooth-on
:nonumber:

$f$ is *$L$-smooth over $C$* if $f(y) \le f(x) + f'(x)(y - x) + \tfrac{L}{2}\|y - x\|^2$ for all
$x, y \in C$.
```

```{prf:definition} Hölderian error bound
:label: def-frank-wolfe-core-heb
:nonumber:

Let $X^\star$ be the set of minimizers of $f$ over $C$. The function $f$ satisfies a
*$(\mu, \theta)$-Hölderian error bound* on $C$, usually with $\mu > 0$ and $\theta \in [0, 1/2]$,
if $\operatorname{dist}(x, X^\star) \le \mu \, (f(x) - f(x^\star))^\theta$ for all $x \in C$ and
$x^\star \in X^\star$.
```

Strong convexity is Mathlib's `StrongConvexOn`: $f$ is *$\mu$-strongly convex on $C$* if $C$ is
convex and
$f(\lambda x + (1 - \lambda) y) \le \lambda f(x) + (1 - \lambda) f(y) - \lambda (1 - \lambda)
\tfrac{\mu}{2} \|x - y\|^2$ for all $x, y \in C$ and $\lambda \in [0, 1]$.

```{prf:lemma} Runs stay feasible
:label: lem-frank-wolfe-core-run-mem
:nonumber:

The iterates of a Frank–Wolfe run on a convex set $C$ stay in $C$.
```

```{prf:lemma} The iterates form a run
:label: lem-frank-wolfe-core-iterates-run
:nonumber:

For a linear minimization oracle and step sizes in $[0, 1]$, the iterates of the Frank–Wolfe
algorithm started in $C$ form a run, with atoms $v_t = \mathrm{lmo}(f'(x_t))$.
```

```{prf:lemma} Smoothness over every set
:label: lem-frank-wolfe-core-smooth-on
:nonumber:

An $L$-smooth function is $L$-smooth over every set.
```

```{prf:lemma} Primal progress of a run
:label: lem-frank-wolfe-core-run-progress
:nonumber:

In a Frank–Wolfe run on a convex set $C$ for a function that is $L$-smooth over $C$,
$f(x_{t+1}) \le f(x_t) - \gamma_t f'(x_t)(x_t - v_t) + \gamma_t^2 \tfrac{L}{2} \|v_t - x_t\|^2$.
```

```{prf:lemma} Scaling from a Hölderian error bound
:label: lem-frank-wolfe-core-heb-scaling
:nonumber:

Let $C$ be compact, and let $f$ be convex over $C$, differentiable at the points of $C$ and
satisfy a $(\mu, \theta)$-Hölderian error bound. If $x \in C$ has primal gap
$h = f(x) - f(x^\star) > 0$, then a nearest minimizer $y$ satisfies
$h^{1 - \theta} \|x - y\| \le \mu \, f'(x)(x - y)$. In particular,
$h^{1 - \theta} \le \mu \|f'(x)\|$.
```

Convexity gives $h \le f'(x)(x - y)$, and the error bound gives $\|x - y\| \le \mu h^\theta$;
multiplying the two by $h^{1-\theta}$ and $\mu$ proves the claim.

```{prf:lemma} First-order strong convexity
:label: lem-frank-wolfe-core-strong-first-order
:nonumber:

If $f$ is $\mu$-strongly convex on $C$ and differentiable at $x \in C$, then
$f(x) + f'(x)(y - x) + \tfrac{\mu}{2} \|y - x\|^2 \le f(y)$ for all $y \in C$. For $\mu = 0$, this
is first-order convexity over $C$.
```

```{prf:lemma} Strong convexity gives an error bound
:label: lem-frank-wolfe-core-strong-heb
:nonumber:

If $f$ is $\mu$-strongly convex on $C$ with $\mu > 0$, then
$\tfrac{\mu}{2} \|x - x^\star\|^2 \le f(x) - f(x^\star)$ for every minimizer $x^\star$ and every
$x \in C$. So $f$ satisfies a $(\sqrt{2/\mu}, 1/2)$-Hölderian error bound on $C$.
```

Both follow from the definition of strong convexity by letting $\lambda \to 0$; neither needs
differentiability of $f$ elsewhere. The run of
[Beyond short steps in Frank–Wolfe algorithms](../frank-wolfe-beyond-short-steps/index.md) and the
sharpness of
[Conditional gradient methods: AdaFW, LazyFW, LazyAFW, NEP-FW and BCG](../conditional-gradient-improvements/index.md)
are the same notions; those entries keep their own definitions.

## Polytopes

Many Frank–Wolfe variants work over a polytope $\operatorname{conv} V$ for a finite set $V$, and their
analysis needs a little polyhedral geometry. The core provides it in finite-dimensional real normed
spaces.

```{prf:definition} Finitely generated cone
:label: def-frank-wolfe-core-cone
:nonumber:

The cone generated by a finite set $G$ consists of the nonnegative combinations
$\sum_{g \in G} c_g g$, $c_g \ge 0$.
```

```{prf:definition} Exposed face
:label: def-frank-wolfe-core-face
:nonumber:

The exposed face of $\operatorname{conv} V$ for a functional $\psi$ has the vertices of $V$ that
maximize $\psi$.
```

```{prf:definition} Minimal face
:label: def-frank-wolfe-core-minface
:nonumber:

The minimal face of a point $y$ has the vertices of $V$ that lie in every exposed face whose
functional is maximized over $V$ at $y$.
```

```{prf:theorem} Farkas lemma
:label: thm-frank-wolfe-core-farkas
:nonumber:

A point outside the cone generated by a finite set $G$ is separated from it by a functional
$\psi$ with $\psi(g) \le 0$ for all $g \in G$ and $\psi(x) > 0$.
```

The proof shows that finitely generated cones are closed, by a conic Carathéodory argument, and
separates with the Hahn–Banach theorem.

```{prf:theorem} The minimal face of a point
:label: thm-frank-wolfe-core-minface
:nonumber:

For $y \in \operatorname{conv} V$, the minimal face of $y$ is an exposed face whose convex hull
contains $y$, and every vertex $v$ of it can be pushed away from: $(1 + \gamma) y - \gamma v \in
\operatorname{conv} V$ for some $\gamma > 0$.
```

The last property follows from the Farkas lemma applied to the cone generated by the directions
$w - y$, $w \in V$.

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
