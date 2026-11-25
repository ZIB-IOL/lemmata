---
title: Frank–Wolfe beyond 1/t under local dual sharpness
numbering:
  headings: false
---

```{include} ../_generated/provenance/frank-wolfe-local-dual-sharpness.md
```

The Frank–Wolfe algorithm [@frank1956algorithm; @levitin1966constrained] minimizes a smooth
convex function over a compact convex set with nothing but a linear minimization oracle, and it
converges at the rate $O(1/t)$ [@jaggi2013revisiting]. In general this cannot be improved
[@canon1968tight; @lan2013complexity]. The paper formalized here locates the obstruction in the
geometry of the feasible region near the minimizers. If the region, together with its oracle, is
*locally dually sharp* there, then Frank–Wolfe converges faster than $1/t$ for every smooth
convex objective. This holds for short steps, exact line search and the classical open-loop
steps alike, with no growth condition on the objective.

This entry covers Propositions 2.2, 3.4, 3.7 and A.2, Theorems 3.5, 3.6, 3.9, 3.10 and 4.2,
Corollary 3.8 and Lemma A.1 of *Frank–Wolfe Beyond 1/t Convergence*. The numbering below is the
paper's; the arXiv version and the NeurIPS 2026 camera-ready agree. The paper contains the
proofs. The Lean statements are slightly more general than the paper's; see
[what the formalization adds](#sec-frank-wolfe-local-dual-sharpness-scope).

```{mermaid}
flowchart LR
  UC["uniformly convex region<br/>(Def. 2.4, Lemma A.1)"] -->|Prop. 3.4| LDS["local dual sharpness<br/>(Def. 3.1)"]
  PATCH["curved patch with<br/>residual gap (Prop. A.2)"] --> LDS
  LDS --> C35["short step, line search:<br/>conditional form (Thm. 3.5)"]
  C35 --> Z36["zero gradient at a<br/>minimizer (Thm. 3.6)"]
  LDS --> P37["gradient bounded<br/>away from 0 (Prop. 3.7)"]
  Z36 --> C38["o(1/t) for every smooth<br/>convex f (Cor. 3.8)"]
  P37 --> C38
  LDS --> C39["open loop:<br/>conditional form (Thm. 3.9)"]
  C39 --> T310["open loop: o(1/t)<br/>(Thm. 3.10)"]
  LDS --> T42["rates under a local<br/>error bound (Thm. 4.2)"]
  HEB["local Hölder error<br/>bound (Def. 4.1)"] --> T42
```

## The algorithm and the 1/t barrier

```{prf:definition} Standing assumptions
:label: def-frank-wolfe-local-dual-sharpness-setting
:nonumber:

The feasible region $C$ is a compact convex subset of a real Hilbert space, and
$\mathrm{lmo}$ is a *linear minimization oracle* for it: for every direction $g$ it returns a
point $\mathrm{lmo}(g) \in \operatorname{argmin}_{y \in C} \langle g, y\rangle$, chosen by a
fixed rule when there are several. The objective $f$ is convex and differentiable, and
$L$-smooth for some $L > 0$: its gradient $\nabla f$ is $L$-Lipschitz.
```

```{prf:definition} The Frank–Wolfe algorithm
:label: def-frank-wolfe-local-dual-sharpness-fw
:nonumber:

Starting from $x_0 \in C$, Frank–Wolfe takes the atom $s_t = \mathrm{lmo}(\nabla f(x_t))$ and
moves toward it, $x_{t+1} = x_t + \gamma_t (s_t - x_t)$, with step size $\gamma_t \in [0,1]$
given by one of three rules:

- the *open-loop* rule $\gamma_t = 2/(t+2)$;
- the *short step* $\gamma_t = \min\{g_t/(L \|s_t - x_t\|^2), 1\}$, where
  $g_t = \langle \nabla f(x_t), x_t - s_t\rangle$ is the *Frank–Wolfe gap*;
- *exact line search*: $\gamma_t$ minimizes $f(x_t + \gamma (s_t - x_t))$ over
  $\gamma \in [0, 1]$, chosen by a fixed rule when there are several minimizers.
```

The iterates stay in $C$ because they are convex combinations; no projection is ever needed.
Write $f^\star = \min_C f$, $\mathcal{M} = \operatorname{argmin}_C f$ for the minimizer set,
and $F_t = f(x_t) - f^\star$ for the primal gap.

```{prf:proposition} $O(1/t)$ convergence
:label: prop-frank-wolfe-local-dual-sharpness-standard
:enumerator: 2.2

Under the standing assumptions, with any of the three step-size rules,
$F_t \le 2 L D^2/(t+2)$ for every $t \ge 1$, where $D$ is the diameter of $C$.
```

Why not better? Each step makes progress in proportion to the gap and inversely to the
distance to the atom: for short steps,
$F_t - F_{t+1} \ge \tfrac12 \min\{g_t,\ g_t^2/(L\|s_t - x_t\|^2)\}$, and $g_t \ge F_t$ by
convexity. On a polygon whose minimizer lies inside an edge, the atoms keep jumping between the
two endpoints of that edge, so $\|s_t - x_t\|$ never becomes small. The iterates zig-zag toward
the edge, and the guaranteed progress, of order $F_t^2$, gives no more than $1/t$. In this
regime the zig-zag really is that slow [@canon1968tight]. Known ways around it assume something
about the objective or about where its minimizer lies: an interior minimizer
[@guelat1986some], a gradient bounded away from zero on a strongly convex region, a strongly
convex objective on a strongly convex region [@garber2015faster], or an error bound on a
uniformly convex region [@kerdreux2021projection]; see [@braun2025conditional] for the whole
landscape.

## Curvature, as the oracle sees it

The cure for the zig-zag is a curved boundary: on a curved region, a small gap forces the atom
to be close.

```{prf:definition} Uniform convexity
:label: def-frank-wolfe-local-dual-sharpness-uc
:enumerator: 2.4

Let $\alpha > 0$ and $q \ge 2$. The set $C$ is *$(\alpha, q)$-uniformly convex* if for all
$x, y \in C$, every $\lambda \in [0,1]$ and every unit vector $z$,
$\lambda x + (1-\lambda) y + \lambda (1-\lambda)\, \alpha \|x - y\|^q z \in C$.
```

The case $q = 2$ is strong convexity of the set (a disk, an ellipse); $\ell_p$ balls with
$p > 2$ are uniformly convex with $q = p$ but not strongly convex.

```{prf:lemma} The gap controls the distance to the atom
:label: lem-frank-wolfe-local-dual-sharpness-uc-gap
:enumerator: A.1

Let $C$ be $(\alpha, q)$-uniformly convex, $x \in C$, and let $s$ minimize
$\langle g, \cdot\rangle$ over $C$. Then
$\tfrac{\alpha}{2} \|g\| \, \|x - s\|^q \le \langle g, x - s\rangle$.
```

The lemma only ever looks at the atoms the oracle returns, and the convergence proofs only need
it near the minimizers. That is the paper's central definition.

```{prf:definition} Local dual sharpness
:label: def-frank-wolfe-local-dual-sharpness-lds
:enumerator: 3.1

Let $M \subseteq C$ be nonempty, $A > 0$ and $q \ge 2$. The region $C$ together with its oracle
satisfies *local dual sharpness around $M$ with constants $(A, q)$* if there is $\rho > 0$ such
that every $x \in C$ with $\operatorname{dist}(x, M) < \rho$ satisfies, for every direction $g$
and the atom $s = \mathrm{lmo}(g)$,
$A \|g\| \, \|x - s\|^q \le \langle g, x - s\rangle$.
```

```{prf:proposition} Uniform convexity implies local dual sharpness
:label: prop-frank-wolfe-local-dual-sharpness-uc-lds
:enumerator: 3.4

If $C$ is $(\alpha, q)$-uniformly convex, then every oracle for $C$ satisfies local dual
sharpness around every nonempty $M \subseteq C$ with constants $(\alpha/2, q)$.
```

Local dual sharpness is genuinely weaker. It holds around any minimizer in the interior of $C$
(the gap is then at least $\|g\|$ times the distance to the boundary), and around minimizers on
a curved part of a region that is flat elsewhere, such as the round caps of a stadium, but not
on its flat sides. The next proposition is the paper's criterion for such patches.

```{prf:proposition} A curved patch with a residual gap
:label: prop-frank-wolfe-local-dual-sharpness-patch
:enumerator: A.2

Let $M \subseteq C$, let $K$ be $(\alpha, q)$-uniformly convex with $q \ge 2$, and let
$\rho, \beta > 0$. Suppose every $x \in C$ with $\operatorname{dist}(x, M) < \rho$ lies in $K$,
and that for every direction $g$ the atom $s = \mathrm{lmo}(g)$ either lies in $K$ and supports
it, $\langle g, y - s\rangle \ge 0$ for all $y \in K$, or leaves a residual gap,
$\beta \|g\| \le \langle g, x - s\rangle$. Then the oracle satisfies local dual sharpness
around $M$ with constants
$\left(\min\{\alpha/2,\ \beta / \max\{1, \operatorname{diam}(C)^q\}\},\ q\right)$.
```

## See it

Below, Frank–Wolfe minimizes $f(x) = \tfrac12 \|x - c\|^2$ (so $L = 1$) over four regions in
the plane. Drag the target $c$. The squares are the most recent atoms $s_t$, the dashed segment
is the current step, and the right panel plots $(t+2)\,F_t$ against $t$ on logarithmic axes.
A falling curve means $F_t = o(1/t)$; a level curve is the $1/t$ barrier. The line below the
plot shows the current step length $\|s_t - x_t\|$: it stays large on flat parts and shrinks
where local dual sharpness holds.

```{anywidget} ./widgets/fw.mjs
:css: ./widgets/fw.css
{"region": "square", "rule": "short", "cx": 0, "cy": 1.45}
```

Things to try, with short steps:

- **Square.** The minimizer lies inside the top edge. The atoms flip between the two top
  corners, the iterates zig-zag, and the curve levels off.
- **Disk**, same $c$. The disk is strongly convex and $\nabla f(x^\star) \ne 0$: by
  [](#prop-frank-wolfe-local-dual-sharpness-lbg) with $q = 2$ the convergence is linear, and
  the curve drops off the chart.
- **$\ell_4$ ball**, same $c$. The minimizer $(0, 1)$ is a point where the boundary is flat to
  second order, so only $q = 4$ is available. The curve becomes a straight line of slope $-1$:
  $F_t \sim t^{-2} = t^{-q/(q-2)}$, the rate of [](#prop-frank-wolfe-local-dual-sharpness-lbg).
- **Stadium.** The minimizer lies on a flat side and the curve levels off, as for the square.
  Now drag $c$ to the right until $x^\star$ moves onto the round cap: the curve falls.
- **Move $c$ inside** any region. The minimizer is interior and $\nabla f$ vanishes there,
  the case of [](#thm-frank-wolfe-local-dual-sharpness-zgm).

With open-loop steps, the curved regions give $o(1/t)$ as in
[](#thm-frank-wolfe-local-dual-sharpness-open-loop). The square falls too: on polytopes,
open-loop steps can be accelerated by a different mechanism, which the paper's related-work
section discusses.

## Short steps and exact line search

Local dual sharpness turns the progress inequality above into something better than $F_t^2$,
because the step length $\|s_t - x_t\|$ now shrinks with the gap. How much better depends on
whether the gradient vanishes at the minimizers. First, the conditional form, which drives
everything else.

```{prf:theorem} Short steps or line search: conditional form
:label: thm-frank-wolfe-local-dual-sharpness-conditional
:enumerator: 3.5

Assume local dual sharpness around a nonempty $M \subseteq C$ with constants $(A, q)$. Let
$x^\star \in C$, and let $p_t \in M$ satisfy $f(p_t) = f(x^\star)$ and $\nabla f(p_t) = 0$ for
all $t$. If the short-step or line-search iterates satisfy $\|x_t - p_t\| \to 0$, then
$(t+2)\,(f(x_t) - f(x^\star)) \to 0$.
```

```{prf:theorem} A minimizer with zero gradient
:label: thm-frank-wolfe-local-dual-sharpness-zgm
:enumerator: 3.6

Assume local dual sharpness around the minimizer set $\mathcal{M}$. If some $x^\star \in
\mathcal{M}$ has $\nabla f(x^\star) = 0$, then short steps and exact line search satisfy
$F_t = o(1/t)$.
```

```{prf:proposition} A gradient bounded away from zero
:label: prop-frank-wolfe-local-dual-sharpness-lbg
:enumerator: 3.7

Assume local dual sharpness around $\mathcal{M}$ with constants $(A, q)$, and
$\|\nabla f(x)\| \ge G > 0$ on $C$. Then short steps and exact line search satisfy:

1. if $q = 2$, with $\kappa = \tfrac12 \min\{1, AG/L\}$, there is $t_0$ such that
   $F_t \le (1-\kappa)^{t - t_0} F_{t_0}$ for all $t \ge t_0$;
2. if $q > 2$, there are $t_0$ and $K > 0$ such that
   $F_t \le K/(t - t_0 + 1)^{q/(q-2)}$ for all $t \ge t_0$.
```

The two cases together cover every smooth convex objective; this is the main result.

```{prf:corollary} Beyond $1/t$
:label: cor-frank-wolfe-local-dual-sharpness-beyond
:enumerator: 3.8

Under the standing assumptions, if $C$ with its oracle satisfies local dual sharpness around
the minimizer set $\mathcal{M}$, then short steps and exact line search satisfy
$F_t = o(1/t)$.
```

```{prf:proof} of [](#cor-frank-wolfe-local-dual-sharpness-beyond)
:nonumber:

If $\nabla f(y) = 0$ for some $y \in C$, then $y$ is a minimizer by convexity, and
[](#thm-frank-wolfe-local-dual-sharpness-zgm) applies. Otherwise $\nabla f$ has no zero on the
compact set $C$, so by continuity $\min_C \|\nabla f\| > 0$, and the $o(1/t)$ conclusion behind
[](#prop-frank-wolfe-local-dual-sharpness-lbg) applies.
```

The paper's Lean development formalized the two branches separately and left this combination
to the text; here the corollary is a single Lean theorem. The improvement holds for each fixed instance. The uniform
$\Omega(1/t)$ lower bounds use instances that change with $t$, for example in growing dimension,
so they do not contradict it.

## The open-loop step size

With $\gamma_t = 2/(t+2)$ there is no one-step contraction, and the argument is more involved;
in exchange, no case distinction on the gradient is needed.

```{prf:theorem} Open loop: conditional form
:label: thm-frank-wolfe-local-dual-sharpness-conditional-ol
:enumerator: 3.9

Assume local dual sharpness around a nonempty $M \subseteq C$ with constants $(A, q)$. Let
$x^\star \in \mathcal{M}$, and let $p_t \in M$ satisfy $f(p_t) = f(x^\star)$ for all $t$. If the
open-loop iterates satisfy $\|x_t - p_t\| \to 0$, then $(t+2)\, F_t \to 0$.
```

```{prf:theorem} Open loop beyond $1/t$
:label: thm-frank-wolfe-local-dual-sharpness-open-loop
:enumerator: 3.10

Under the standing assumptions, if $C$ with its oracle satisfies local dual sharpness around
$\mathcal{M}$, then the open-loop iterates satisfy $F_t = o(1/t)$.
```

## Rates under a local error bound

Local dual sharpness alone gives $o(1/t)$ but no rate. Growth of $f$ away from its minimizers
quantifies it.

```{prf:definition} Local Hölder error bound
:label: def-frank-wolfe-local-dual-sharpness-heb
:enumerator: 4.1

Let $r \ge 2$. The objective $f$ satisfies a *local Hölder error bound of order $r$* around
$\mathcal{M}$ if there are $B, \rho > 0$ with
$\operatorname{dist}(x, \mathcal{M})^r \le B\,(f(x) - f^\star)$ for every $x \in C$ with
$\operatorname{dist}(x, \mathcal{M}) < \rho$.
```

```{prf:theorem} Quantitative rates
:label: thm-frank-wolfe-local-dual-sharpness-heb
:enumerator: 4.2

Assume local dual sharpness around $\mathcal{M}$ with constants $(A, q)$, $q \ge 2$, and a
local Hölder error bound of order $r \ge 2$. Then for the short step, exact line search and the
open-loop rule there are $t_0$ and $K > 0$ such that
$F_t \le K/(t - t_0 + 1)^{rq/(rq-2)}$ for all $t \ge t_0$.
```

For a strongly convex region and quadratic growth, $q = r = 2$, the exponent is $2$: the
$O(1/t^2)$ rate known for strongly convex objectives on strongly convex sets
[@garber2015faster], now from local assumptions only.

(sec-frank-wolfe-local-dual-sharpness-scope)=
## What the formalization adds

The statements are in `Statement.lean`, separate from the proofs, and are proved in
`Main.lean` from the development in `Proof/`. Compared with the paper they are:

- **in a real Hilbert space** instead of $\mathbb{R}^d$;
- **for every oracle and every line-search rule.** The paper fixes one deterministic rule for
  breaking ties between minimizers; every statement here holds for each such rule;
- **in Mathlib's terms**: $f$ is assumed `Differentiable`, `ConvexOn` the whole space, and
  `LipschitzWith L (∇ f)`.

Corollary 3.8, and Theorem 4.2 for the open-loop rule, are single theorems. Two assumptions that
the original Lean development needed and the paper does not make are gone: a positive gap at
every step in Theorem 3.5, and a bound on the initial gap in Theorem 3.6.

Not covered: Proposition 2.1 and Lemmas 2.3 and 2.5 are used inside the proofs but not
exported. The examples beyond uniformly convex sets (Example A.3, including the stadium),
Remark A.4 on strict convexity, the computational example, and the generalized open-loop rules
$\gamma_t = \ell/(t + \ell)$ of Remark A.7 are not formalized as statements here.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FrankWolfeLDS/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-local-dual-sharpness.md
```
