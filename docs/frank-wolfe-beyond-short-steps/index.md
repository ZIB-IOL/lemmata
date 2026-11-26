---
title: "Beyond short steps in Frank–Wolfe algorithms"
numbering:
  headings: false
---

```{include} ../_generated/provenance/frank-wolfe-beyond-short-steps.md
```

The Frank–Wolfe algorithm [@frank1956algorithm] moves from $x_t$ toward an atom
$v_t \in \operatorname{argmin}_{v \in C} f'(x_t)(v)$ with a step size $\gamma_t \in [0, 1]$. Its
classical guarantees bound the *primal gap* $f(x_t) - f(x^*)$, which cannot be computed because
$f(x^*)$ is unknown. The short step chooses $\gamma_t$ to maximize the decrease of $f$ that
smoothness guarantees. This entry formalizes the primal-dual short steps of @martinezrubio2025beyond:
step sizes that maximize the guaranteed decrease of a *computable* gap instead, with the same
convergence rate. The objects (smoothness, the oracle) are those of
[Frank–Wolfe: the core](../frank-wolfe-core/index.md); the numbering is the paper's.

## Runs and the primal-dual gap

Step-size rules such as the primal-dual short step depend on the whole history of the run, so the
statements are about runs rather than about one fixed step-size function.

```{prf:definition} Frank–Wolfe run
:label: def-frank-wolfe-beyond-short-steps-run
:nonumber:

A *Frank–Wolfe run* on $C$ consists of sequences $x_t$, $v_t$, $\gamma_t$ with $x_0 \in C$,
$v_t \in \operatorname{argmin}_{v \in C} f'(x_t)(v)$, $\gamma_t \in [0, 1]$ and
$x_{t+1} = x_t + \gamma_t (v_t - x_t)$. Every tie-breaking rule of the oracle and every step-size
rule gives a run.
```

Every iterate gives a lower bound on the optimal value: by convexity,
$f(y) \ge f(x_\ell) + f'(x_\ell)(y - x_\ell) \ge f(x_\ell) - g_\ell$ for all $y \in C$, where
$g_\ell = f'(x_\ell)(x_\ell - v_\ell)$ is the Frank–Wolfe gap. A weighted average of these bounds
is again a lower bound, and the step sizes fix the weights.

```{prf:definition} Primal-dual gap
:label: def-frank-wolfe-beyond-short-steps-gap
:nonumber:

For a run, let $L_0 = f(x_0) - g_0$ and $L_t = (1 - \gamma_t) L_{t-1} + \gamma_t (f(x_t) - g_t)$
for $t \ge 1$. The *primal-dual gap* is $G_t = f(x_{t+1}) - L_t$. With weights $a_\ell > 0$,
$A_t = a_0 + \dots + a_t$ and $\gamma_t = a_t / A_t$, this is the paper's
$L_t = \frac{1}{A_t}\sum_{\ell \le t} a_\ell (f(x_\ell) - g_\ell)$.
```

The upper bound $f(x_{t+1})$ is one step ahead of the lower bound $L_t$; this shift is what makes
the recursion below exact.

```{prf:lemma} The primal-dual gap bounds the primal gap
:label: lem-frank-wolfe-beyond-short-steps-valid
:nonumber:

For a convex differentiable $f$ and every run, $f(x_{t+1}) - f(y) \le G_t$ for all $y \in C$ and
all $t$. In particular $G_t \ge f(x_{t+1}) - \min_C f \ge 0$, and $G_t \le \varepsilon$ certifies
an $\varepsilon$-solution.
```

## Primal-dual short steps

The definitions give the gap recursion directly. The paper states it as an inequality, which also
covers the heavy-ball variant; for Frank–Wolfe it is an identity.

```{prf:proposition} Gap recursion
:label: prop-frank-wolfe-beyond-short-steps-recursion
:enumerator: 4.1

For every run and $t \ge 1$,
$G_t = (1 - \gamma_t) G_{t-1} - \gamma_t f'(x_t)(v_t - x_t) - f(x_t) + f(x_t + \gamma_t (v_t - x_t))$.
```

```{prf:proposition} Convexity in the step size
:label: prop-frank-wolfe-beyond-short-steps-convex
:enumerator: 4.1

For a convex $f$, the right-hand side of the gap recursion is a convex function of the step size,
so minimizing it is a one-dimensional convex problem.
```

Smoothness bounds the right-hand side by $(1 - \gamma) G_{t-1} + \gamma^2 \frac{L}{2}\|v_t - x_t\|^2$.
Minimizing this quadratic over $[0, 1]$ gives the *primal-dual short step*.

```{prf:definition} Primal-dual short step
:label: def-frank-wolfe-beyond-short-steps-step
:nonumber:

$\gamma_t = \min\{1, G_{t-1} / (L \|v_t - x_t\|^2)\}$, and $\gamma_t = 1$ when $v_t = x_t$.
```

If $G_{t-1}$ is replaced by the primal gap $f(x_t) - f(x^*)$, the same computation gives the
classical short step. The primal-dual short step needs no knowledge of $f(x^*)$.

```{prf:proposition} Rate of primal-dual short steps
:label: prop-frank-wolfe-beyond-short-steps-rate
:enumerator: 4.1

Let $C$ be compact and convex with diameter $D$, and let $f$ be convex and $L$-smooth. Take a run
with $\gamma_0 = 1$ in which every later step size is the open-loop step $2/(t+2)$, a minimizer of
the smoothness bound over $[0, 1]$, or a minimizer of the right-hand side of the gap recursion over
$[0, 1]$ (line search on the primal-dual gap). The rule may change from one iteration to the next.
Then $G_t \le 2LD^2/(t+2)$ for all $t$.
```

```{prf:proposition} The explicit primal-dual short step
:label: prop-frank-wolfe-beyond-short-steps-short-step
:enumerator: 4.1

Under the same assumptions and with $L > 0$, the primal-dual short step with $\gamma_0 = 1$ gives
$G_t \le 2LD^2/(t+2)$ for all $t$.
```

The paper proves $G_t \le 4LD^2/(t+2)$ for the two new rules, by turning the contraction
$G_t \le (1 - \gamma_t/2) G_{t-1}$ into a rate. The formal proof compares every rule with the
open-loop step instead: each of them gives
$G_t \le (1 - s) G_{t-1} + s^2 \frac{L}{2} D^2$ at $s = 2/(t+2)$, and this recursion gives the
constant $2$. It is the same rate as the classical primal analysis, now for a computable gap.

## Racing the rules

The widget runs Frank–Wolfe with five step-size rules from the same start, on
$f(x) = \frac12 (x - c)^\top Q (x - c)$ with $Q = \operatorname{diag}(1, \mu)$, so $L = 1$. The chart
shows the computable gap $G_t$ of every rule on log–log axes, with the guarantee $2LD^2/(t+2)$
dashed. Drag $c$, switch the region and the objective, and toggle the rules.

```{anywidget} ./widgets/pd.mjs
:css: ./widgets/pd.css
{"region": "square", "objective": "elongated", "cx": 1.35, "cy": 0.55, "rules": "open,short,pd,ls,hb", "primal": false}
```

Things to try:

- **Classical short step.** Its own gap, built from its own step sizes, can stall far above the
  guarantee: when $v_t = x_t$ the short step is $0$, so new lower bounds get no weight. With $c$
  near a corner of the square, the iterate reaches $x^*$ at once and the gap never moves. The
  primal-dual short step takes $\gamma_t = 1$ there and certifies optimality immediately.
- **Elongated objective.** The smoothness bound with $L = 1$ overestimates the curvature along the
  second axis, so line search on the primal-dual gap pulls ahead of the primal-dual short step.
  With the round objective the bound is exact and the two rules coincide.
- **Heavy ball.** Averaging the gradients gives a tighter lower bound, and its gap is often the
  smallest.
- **Primal gaps.** Switch them on to see $f(x_{t+1}) - f(x^*) \le G_t$ for every rule.

## Heavy-ball Frank–Wolfe

Heavy-ball Frank–Wolfe asks the oracle about the average of the derivatives seen so far instead
of the current one, and its lower bound minimizes the average of the linear models.

```{prf:definition} Heavy-ball run
:label: def-frank-wolfe-beyond-short-steps-hb-run
:nonumber:

Let $\bar g_0 = f'(x_0)$ and $\bar g_t = (1 - \gamma_t)\bar g_{t-1} + \gamma_t f'(x_t)$. A
*heavy-ball run* is a run in which every $v_t$ minimizes $\bar g_t$ over $C$ instead of
$f'(x_t)$.
```

```{prf:definition} Heavy-ball primal-dual gap
:label: def-frank-wolfe-beyond-short-steps-hb-gap
:nonumber:

Let $c_0 = f(x_0) - f'(x_0)(x_0)$ and $c_t = (1 - \gamma_t) c_{t-1} + \gamma_t (f(x_t) - f'(x_t)(x_t))$,
so that $c_t + \bar g_t(y)$ is the weighted average of the linear models
$f(x_\ell) + f'(x_\ell)(y - x_\ell)$. The lower bound is $L_t = c_t + \bar g_t(v_t)$, the minimum of
this average over $C$, and the gap is $G_t = f(x_{t+1}) - L_t$.
```

```{prf:lemma} The heavy-ball gap bounds the primal gap
:label: lem-frank-wolfe-beyond-short-steps-hb-valid
:nonumber:

For a convex differentiable $f$ and every heavy-ball run, $f(x_{t+1}) - f(y) \le G_t$ for all
$y \in C$.
```

```{prf:proposition} Heavy-ball gap recursion
:label: prop-frank-wolfe-beyond-short-steps-hb-recursion
:enumerator: 4.1

For every heavy-ball run and $t \ge 1$,
$G_t \le (1 - \gamma_t) G_{t-1} - \gamma_t f'(x_t)(v_t - x_t) - f(x_t) + f(x_t + \gamma_t (v_t - x_t))$.
```

```{prf:proposition} Heavy-ball rate
:label: prop-frank-wolfe-beyond-short-steps-hb-rate
:enumerator: 4.1

Under the assumptions of the rate for Frank–Wolfe, every heavy-ball run with $\gamma_0 = 1$
whose later step sizes follow the same three rules, for its own gap, satisfies
$G_t \le 2LD^2/(t+2)$.
```

For open-loop steps a heavy-ball run is defined step by step. For the two adaptive rules the atom
$v_t$ depends on $\gamma_t$ through $\bar g_t$, while $\gamma_t$ is computed from $v_t$, so these
rules are conditions that a run satisfies rather than a procedure; the proposition holds for every
run that satisfies them. Both rates come from one lemma: any sequence with
$G_t \le (1 - \gamma_t) G_{t-1} - \gamma_t f'(x_t)(v_t - x_t) - f(x_t) + f(x_t + \gamma_t (v_t - x_t))$
and $G_0 \le \frac{L}{2}D^2$ whose steps follow the three rules satisfies $G_t \le 2LD^2/(t+2)$.

## Not yet covered

The optimistic Frank–Wolfe algorithm (Theorem 3.1) and primal-dual short steps for gradient
descent (Proposition 4.2) are not formalized here.

## The formal statements at a glance

```{literalinclude} ../../lean/Lemmata/FrankWolfeBSS/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/frank-wolfe-beyond-short-steps.md
```
