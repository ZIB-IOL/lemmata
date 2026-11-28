---
numbering:
  headings: false
title: Changelog
---

What changed in the archive that a reader should know about: new entries, corrections to
published entries, and changes to what "checked" means. Routine edits are not listed; every
entry shows its own last change and links to the exact commit.

Newest first. Add an item in the same pull request as the change it describes.

## 2026-11-27

- **Updated entry:** [Frank–Wolfe with simple steps for generalized self-concordant functions](frank-wolfe-generalized-self-concordant/index.md), adding blended pairwise conditional gradients with backtracking and its linear rate over polytopes (Theorem 3.2).
- **Updated entry:** [Frank–Wolfe with simple steps for generalized self-concordant functions](frank-wolfe-generalized-self-concordant/index.md), adding away-step Frank–Wolfe with backtracking and its linear rate over polytopes (Theorem 3.2).
- **Updated entry:** [Frank–Wolfe with simple steps for generalized self-concordant functions](frank-wolfe-generalized-self-concordant/index.md), adding Frank–Wolfe with backtracking and its improved rates for an interior minimizer and over uniformly convex sets (Theorems 2.11, 2.15 and 2.16), with an erratum for the contraction lemma (Lemma 2.14).
- **New entry:** [Frank–Wolfe with simple steps for generalized self-concordant functions](frank-wolfe-generalized-self-concordant/index.md), formalizing the monotonic Frank–Wolfe algorithm of Carderera, Besançon and Pokutta and its O(1/t) rates for the primal gap and the Frank–Wolfe gap, under the local descent property that generalized self-concordance provides.
- **Updated entry:** [Linear convergence of Frank–Wolfe over product polytopes](frank-wolfe-product-polytopes/index.md), adding facets, the vertex-facet distance and its value for a product of two polytopes (Proposition 4.7).
- **Updated entry:** [Linear convergence of Frank–Wolfe over product polytopes](frank-wolfe-product-polytopes/index.md), adding the upper bound for the pyramidal width of a product (Theorem 4.5) and the linear rate of away-step Frank–Wolfe over a product of two polytopes under quadratic growth (Proposition 4.8).
- **Updated entry:** [Linear convergence of Frank–Wolfe over product polytopes](frank-wolfe-product-polytopes/index.md), adding the affine pyramidal width and the lower bound for the pyramidal width of a product of two polytopes (Theorem 4.5), with a separation lemma for affine hulls and convex hulls.
- **New entry:** [Linear convergence of Frank–Wolfe over product polytopes](frank-wolfe-product-polytopes/index.md), formalizing the objective of the approximate feasibility problem for an intersection of polytopes from the paper by Iommazzo, Martínez-Rubio, Criado, Wirth and Pokutta (convex, 1-smooth and 1-PL) and the bounds on the pyramidal width formula of a product.
- **Updated entry:** [The approximate Carathéodory problem via Frank–Wolfe](frank-wolfe-approximate-caratheodory/index.md), adding the sparsity of Frank–Wolfe iterates and the cardinality bounds for short steps, for targets in the relative interior and for approximate projections onto strongly convex sets (Corollaries 5.1, 5.3 and 7.1).
- **New entry:** [The approximate Carathéodory problem via Frank–Wolfe](frank-wolfe-approximate-caratheodory/index.md), formalizing the objective of the paper by Combettes and Pokutta (differentiable, convex, smooth, gradient dominated and sharp in the ℓp-norm, with the derivative identified via Hölder's inequality) and its Hadamard lower bound, for which the entry supplies a proof.
- **New entry:** [Log-adaptive open-loop step-sizes for Frank–Wolfe](frank-wolfe-log-adaptive-open-loop/index.md), formalizing the paper by Wirth, Peña and Pokutta: the strengthened cumulative-product bound for adaptive open-loop step sizes (corrected to the range in which it holds), the rates under strong and weak growth, and the log-adaptive step sizes with rates Õ(t^(−1/(1−r))) and Õ(t^(−1/(1−r)) + t^(−2)).
- **Updated entry:** [Affine-invariant accelerated rates for Frank–Wolfe with open-loop step-sizes](frank-wolfe-affine-invariant-open-loop/index.md), adding the sufficient conditions for the growth properties (Propositions 2.8, 3.6, 4.3 and 5.3) and errata for Lemma 2.10 and Example 4.4.
- **Updated entry:** [Affine-invariant accelerated rates for Frank–Wolfe with open-loop step-sizes](frank-wolfe-affine-invariant-open-loop/index.md), adding the rates under weak growth (Theorem 4.1 with its dichotomy, Lemma 4.2) and under (relaxed) gaps growth (Theorems 5.1 and 5.2).
- **New entry:** [Affine-invariant accelerated rates for Frank–Wolfe with open-loop step-sizes](frank-wolfe-affine-invariant-open-loop/index.md), formalizing the measures of optimality and Section 3 of the paper by Wirth, Peña and Pokutta: under strong growth, the best duality gap and the smallest Frank–Wolfe gap converge at the rates O(1/t), O(t^(−ℓ)) and O(t^(−ℓ+ε) + t^(−1/(1−r))), with the telescoping bounds for the step sizes.
- **Updated entry:** [Acceleration of Frank–Wolfe algorithms with open-loop step-sizes](frank-wolfe-open-loop-acceleration/index.md), adding Section 4: active set identification, scaling inequalities at the boundary and from strong convexity, the decay of the distance to the optimal face, and the rate O(1/t²) for a minimizer in the relative interior of a face of a polytope (Lemmas 4.1 to 4.4, Theorem 4.5); with Sections 3 and 5 this completes the entry apart from kernel herding.
- **Updated entry:** [Acceleration of Frank–Wolfe algorithms with open-loop step-sizes](frank-wolfe-open-loop-acceleration/index.md), adding Section 5: decomposition-invariant pairwise Frank–Wolfe with the step sizes 8/(t+8) rounded down to powers of 1/2 (Proposition 5.2, Theorem 5.3) and away-step Frank–Wolfe with open-loop step sizes and a count of progress steps (Lemmas 5.5 and 5.6, Proposition 5.7, Theorem 5.9), with an erratum for the first iterate of Algorithm 4.
- **New entry:** [Acceleration of Frank–Wolfe algorithms with open-loop step-sizes](frank-wolfe-open-loop-acceleration/index.md), formalizing Section 3 of the paper by Wirth, Kerdreux and Pokutta: the rate 8Lδ²/(t+3) for the step sizes 4/(t+4), the sequence lemma, and accelerated rates when the minimizers lie in the relative interior, when the gradients are bounded away from zero on a uniformly convex set, and under a Hölderian error bound on a uniformly convex set, with an erratum for the scaling inequality of Lemma 3.2.
- **Updated entry:** [Frank–Wolfe: the core](frank-wolfe-core/index.md), adding Frank–Wolfe runs with arbitrary tie-breaking and step sizes, smoothness over the feasible region, Hölderian error bounds and strong convexity, with the progress bound of a run, the scaling inequality of an error bound and the quadratic growth of strongly convex functions.
- **Updated entry:** [Frank–Wolfe oracle complexity with prescribed set smoothness](frank-wolfe-prescribed-smoothness/index.md) now checks the finite optimal-order corollary, the little-o rate on a fixed norm-compact set, and a fixed-distribution lower bound with unique Hilbert-space oracle replies. For each jointly measurable randomized anytime method, one body gives infinitely many failures with probability at least $1/5$.
- **Updated entry:** [Frank–Wolfe oracle complexity with prescribed set smoothness](frank-wolfe-prescribed-smoothness/index.md): the widget also covers the fixed Hilbert-space example (Frank–Wolfe between the bounds $31/(256(t+1))$ and $2(15/4)^2/(t+2)$, and the single vertical call), plots every method against the number of oracle calls, and computes the optimal value of the body with perturbed vertices accurately; the widget section moves below the Hilbert-space section.
- **Updated entry:** [An information diffusion Fano inequality](information-diffusion-fano/index.md), adding the Fano inequality for independent samples (Corollary 2.4, with an erratum), which completes the entry.
- **Updated entry:** [An information diffusion Fano inequality](information-diffusion-fano/index.md), adding entropy for finite random variables, `I(X; X̂) = H(X) - H(X | X̂)` and the entropy versions of the Fano inequality (Corollaries 2.3 and 2.5).
- **Updated entry:** [An information diffusion Fano inequality](information-diffusion-fano/index.md), adding Rényi divergences and Proposition 2.1 for orders α ≠ 1, with an erratum for α < 1.
- **New entry:** [An information diffusion Fano inequality](information-diffusion-fano/index.md), formalizing the note by Braun and Pokutta: the information diffusion inequality for relative entropy (Proposition 2.1), the Fano inequality for arbitrary relations (Proposition 2.2) and the distance-based and continuous Fano inequalities (Corollaries 2.6 and 2.7).
- **Updated entry:** [Frank–Wolfe oracle complexity with prescribed set smoothness](frank-wolfe-prescribed-smoothness/index.md) adds two kernel-checked Hilbert-space results. One fixed body gives sharp inverse-time error for gradient queries. Each deterministic arbitrary-query strategy also has a single smooth, unique-oracle body that is hard at every budget.
- **Updated entry:** [Lazifying conditional gradient algorithms: LCG, LPCG and parameter-free LCG](lazifying-conditional-gradients/index.md), adding weak separation through augmentation (Proposition 6.1).
- **Updated entry:** [Lazifying conditional gradient algorithms: LCG, LPCG and parameter-free LCG](lazifying-conditional-gradients/index.md), adding lazy pairwise conditional gradients on simplex-like polytopes (Theorem 3.2, with two errata).
- **New entry:** [Lazifying conditional gradient algorithms: LCG, LPCG and parameter-free LCG](lazifying-conditional-gradients/index.md), formalizing the paper by Braun, Pokutta and Zink: weak separation, lazy conditional gradients (Theorem 3.1) and the parameter-free variant (Theorem 4.2, Corollary 4.3).
- **Updated entry:** [Conditional gradient methods: away-step, fully-corrective and pairwise Frank–Wolfe](away-step-frank-wolfe/index.md), adding decomposition-invariant pairwise Frank–Wolfe on simplex-like polytopes (Theorem 3.8 with the rate of its proof, and two errata).
- **Updated entry:** [Conditional gradient methods: AdaFW, LazyFW, LazyAFW, NEP-FW and BCG](conditional-gradient-improvements/index.md), adding away-step Frank–Wolfe under sharpness for θ < 1/2 (Corollary 3.33) and the gradient dominated property of sharp functions (Lemma 3.35).
- **Updated entry:** [Frank–Wolfe oracle complexity with prescribed set smoothness](frank-wolfe-prescribed-smoothness/index.md): the exposition is rewritten in standard terms, and six exported Lean declarations are renamed to match: `lower_bound_vertex_lmo`, `symmetric_thickening_reveals`, `tangent_balls_linear_rate`, `vertexLMO`, `Upper.innerFrankWolfe` and `Joint.projectedGradientRun` (formerly `lower_bound_vertex_rule`, `symmetric_bulge_reveals`, `joint_linear_rate`, `vertexOracle`, `Upper.quadraticMethod` and `Joint.jointRun`). The statements are unchanged.
- **Updated entry:** [Conditional gradient methods: AdaFW, LazyFW, LazyAFW, NEP-FW and BCG](conditional-gradient-improvements/index.md), adding the simplex descent step (Lemma 3.45).
- **Updated entry:** [Conditional gradient methods: AdaFW, LazyFW, LazyAFW, NEP-FW and BCG](conditional-gradient-improvements/index.md), adding blended conditional gradients for strongly convex objectives (Theorem 3.42, with explicit constants).
- **Updated entry:** [Blended pairwise conditional gradients: BPCG and LazyBPCG](blended-pairwise-conditional-gradients/index.md), adding lazified BPCG for strongly convex objectives (Theorem 3.6, case (A), with explicit constants).
- **Updated entry:** [Blended pairwise conditional gradients: BPCG and LazyBPCG](blended-pairwise-conditional-gradients/index.md), adding lazified BPCG for convex objectives (Theorem 3.6, case (B), with explicit constants).
- **Updated entry:** [Conditional gradient methods: AdaFW, LazyFW, LazyAFW, NEP-FW and BCG](conditional-gradient-improvements/index.md), adding blended conditional gradients (Theorem 3.42, convex case, with explicit constants).
- **Updated entry:** [Conditional gradient methods: AdaFW, LazyFW, LazyAFW, NEP-FW and BCG](conditional-gradient-improvements/index.md), adding Frank–Wolfe with the nearest extreme point oracle (Theorem 3.36).
- [Bounds for finite-order Grothendieck constants](grothendieck-lower-bounds/index.md) adds a 301-row witness for $K_G(3)>1.4397098471655953$, its Lean vector and signing proofs, and a reproducible certificate for the exact classical maximum.
- **New entry:** [Frank–Wolfe oracle complexity with prescribed set smoothness](frank-wolfe-prescribed-smoothness/index.md): on convex bodies with $\beta$-Lipschitz unit normals and diameter $D$, every randomized method requiring no more than $T$ linear minimization oracle calls has gap of order $L(D-2/\beta)^2/T$ on some body with unique linear minimizers, even for a known quadratic, and a matching method attains this order; with bounds for feasible and for deterministic methods, a distance penalty, sliding for smooth objectives and a linear rate under inner and outer tangent balls.
- **Updated entry:** [Conditional gradient methods: AdaFW, LazyFW, LazyAFW, NEP-FW and BCG](conditional-gradient-improvements/index.md), adding linear convergence of away-step Frank–Wolfe under sharpness (Corollary 3.33, θ = 1/2) with the constant of the proof and an erratum.
- **Updated entry:** [Conditional gradient methods: AdaFW, LazyFW, LazyAFW, NEP-FW and BCG](conditional-gradient-improvements/index.md), adding sharpness (Definition 3.25) with the primal gap bound (Lemma 3.31) and geometric sharpness (Lemma 3.32).
- **Updated entry:** [Conditional gradient methods: AdaFW, LazyFW, LazyAFW, NEP-FW and BCG](conditional-gradient-improvements/index.md), adding lazy away-step Frank–Wolfe (Theorem 3.16) with a corrected iteration count and an erratum.
- **Updated entry:** [Conditional gradient methods: AdaFW, LazyFW, LazyAFW, NEP-FW and BCG](conditional-gradient-improvements/index.md), adding lazy conditional gradients with a weak separation oracle (Theorem 3.15).
- [Bounds for finite-order Grothendieck constants](grothendieck-lower-bounds/index.md) adds a 141-row witness for $K_G(3)>1.4396139030752404$ and a rotation proof of $K_G(3)<1.451263576$ from the published finite local model of Designolle et al.

## 2026-11-26

- **New entry:** [Blended pairwise conditional gradients: BPCG and LazyBPCG](blended-pairwise-conditional-gradients/index.md), formalizing BPCG from Tsuji, Tanaka and Pokutta: the rate 4LD²/T for convex objectives and linear convergence over polytopes for strongly convex objectives, without swap steps.
- **New entry:** [Conditional gradient methods: AdaFW, LazyFW, LazyAFW, NEP-FW and BCG](conditional-gradient-improvements/index.md), starting with adaptive step sizes (AdaFW, Section 3.1.2 of the book): the backtracking search terminates with an estimate at most max{M₀, τL}, and Frank–Wolfe with these steps keeps the vanilla rates.
- **Updated entry:** [Conditional gradient methods: smoothness, scaling and linear rates](conditional-gradient-basics/index.md), adding Theorem 2.8 (Frank–Wolfe is slow when the minimizers lie on a face) and Lemma 2.10, completing Chapter 2.
- **Updated entry:** [Conditional gradient methods: smoothness, scaling and linear rates](conditional-gradient-basics/index.md), adding Example 2.7 (a primal gap lower bound on the simplex).
- **Updated entry:** [Conditional gradient methods: smoothness, scaling and linear rates](conditional-gradient-basics/index.md), adding Definition 2.12, Proposition 2.19 (scaling for uniformly convex sets), Theorem 2.20 (rates over uniformly convex sets) and Theorem 2.24 (gradient-dominated objectives, with scale-invariant constants).
- **Updated entry:** [Conditional gradient methods: smoothness, scaling and linear rates](conditional-gradient-basics/index.md), adding Theorem 2.2 (vanilla Frank–Wolfe: primal and Frank–Wolfe gap rates), Proposition 2.9 (iterates under fixed step sizes) and Theorem 2.11 (nonconvex objectives).
- **Updated entry:** [Conditional gradient methods: away-step, fully-corrective and pairwise Frank–Wolfe](away-step-frank-wolfe/index.md), adding pairwise Frank–Wolfe (Theorem 3.2): a linear rate with fewer than |V|! consecutive swap steps, proved by a permutation argument.
- **Updated entry:** [Conditional gradient methods: away-step, fully-corrective and pairwise Frank–Wolfe](away-step-frank-wolfe/index.md), adding a corrected Corollary 2.32: a lower bound on the pyramidal width from an inequality description, with an erratum for the book's argument.
- **Updated entry:** [Conditional gradient methods: away-step, fully-corrective and pairwise Frank–Wolfe](away-step-frank-wolfe/index.md), completing Proposition 2.31: the pyramidal width equals the facial distance, in every finite-dimensional real normed space.
- **Updated entry:** [Conditional gradient methods: away-step, fully-corrective and pairwise Frank–Wolfe](away-step-frank-wolfe/index.md), adding Proposition 2.31's lower bound: the facial distance is a scaling constant, so the linear rates hold with it.
- **Updated entry:** [Frank–Wolfe: the core](frank-wolfe-core/index.md), adding polyhedral tools for later entries: closedness of finitely generated cones, the Farkas lemma, and exposed and minimal faces of polytopes.
- **New entry:** [Conditional gradient methods: away-step, fully-corrective and pairwise Frank–Wolfe](away-step-frank-wolfe/index.md), proving that the away-step and fully-corrective Frank–Wolfe algorithms converge linearly over polytopes for smooth strongly convex objectives, with rates governed by the pyramidal width.
- **Updated entry:** [Conditional gradient methods: smoothness, scaling and linear rates](conditional-gradient-basics/index.md), adding Theorem 2.6 on approximate linear minimization, with the error normalized so that the stated rate $2LD^2(1+\delta)/(t+3)$ holds.
- **Updated entry:** [Conditional gradient methods: smoothness, scaling and linear rates](conditional-gradient-basics/index.md), adding Lemma 2.21 on contractions of mixed type; the first bound holds before the cutoff $t_0$, and a counterexample shows it can fail at $t_0$.
- **New entry:** [Conditional gradient methods: smoothness, scaling and linear rates](conditional-gradient-basics/index.md), proving that Frank–Wolfe with short steps or line search converges linearly when the minimizer is interior and the objective is gradient dominated, together with the smoothness, gap and contraction lemmas of the first two chapters of the book.
- **Updated entry:** [Beyond short steps in Frank–Wolfe algorithms](frank-wolfe-beyond-short-steps/index.md), adding heavy-ball Frank–Wolfe with the same primal-dual rate $2LD^2/(t+2)$ and an interactive comparison of the step-size rules.
- **New entry:** [Beyond short steps in Frank–Wolfe algorithms](frank-wolfe-beyond-short-steps/index.md), proving that Frank–Wolfe with primal-dual short steps, line search on the primal-dual gap or open-loop steps, mixed freely, has a computable primal-dual gap of at most $2LD^2/(t+2)$.
- **Updated entry:** [The Frank–Wolfe algorithm: a short introduction](frank-wolfe-introduction/index.md), adding the Frank–Wolfe gap bound $6.75\,LD^2/(t+2)$ of Theorem 4.5, the adaptive step-size lemmas 4.9–4.11 and the approximate Carathéodory theorem 5.1 in $\ell_p$, $p \ge 2$.
- **New entry:** [The Frank–Wolfe algorithm: a short introduction](frank-wolfe-introduction/index.md), proving first-order optimality, a lower bound for any step sizes and the convergence for nonconvex objectives, with the gap inequalities, primal progress and the $O(1/t)$ rate bound to the core.
- **New entry:** [Frank–Wolfe: the core](frank-wolfe-core/index.md), the shared objects of the Frank–Wolfe entries in normed and Hilbert spaces, proving the gap inequalities, the descent and progress lemmas and the classical $O(1/t)$ rate; [Frank–Wolfe beyond 1/t under local dual sharpness](frank-wolfe-local-dual-sharpness/index.md) now builds on it, with its statements unchanged.

## 2026-11-25

- **New entry:** [Frank–Wolfe beyond 1/t under local dual sharpness](frank-wolfe-local-dual-sharpness/index.md), proving that Frank–Wolfe with short steps, exact line search or open-loop steps converges with primal gap $o(1/t)$ for every smooth convex objective when the feasible region and its oracle are locally dually sharp around the minimizers.

## 2026-11-22

- **New entry:** [Facet lifting and frequency certificates for symmetric Bell polytopes](symmetric-bell-facet-lifting/index.md), showing that a facet of the three-party, four-setting symmetry projection lifts to a face strictly inside another proper face, and proving the cross-polytope equivalence for two through five settings.
- **New entry:** [Exact Bell values and local visibility for the E₈ root correlations](modified-e8-bell/index.md), proving the classical value $6104$, the vector value $9240$ and the local visibility $109/165$ of the modified $E_8$ Bell matrix.
- **New entry:** [Improved lower bounds for finite-order Grothendieck constants](grothendieck-lower-bounds/index.md), proving $K_G(3)>1.43888070193021$ in Lean from the classical value of an explicit matrix, established by an exhaustive search, and improving the vectors for orders five and six.
- **New entry:** [The exact classical value of the Fishburn–Reeds matrices](fishburn-reeds-classical-bound/index.md), proving the all-order fixed-shift formula and determining the optimal uniform diagonal shifts in dimensions seven through ten.
- **New entry:** [Exact LP extension complexity of planar Steiner tree polytopes](planar-steiner-extension-complexity/index.md), showing that the Steiner tree polytopes of planar graphs have worst-case linear extension complexity $2^{\Theta(\sqrt n)}$, already for two cofacial terminals, with the reduction chain behind the lower bound formalized in Lean.

## 2026-11-21

- **New entry:** [On the Existence Spectrum of Steiner Systems S(2,6,n)](steiner-six-spectrum/index.md), settling 24 previously unresolved orders and leaving only 51, 61, and 81 open.

## 2026-11-16

- **New entry:** [Isotropy and Finite-Spacing Error of the C19 Cubic Symbol](c19-isotropic-symbol/index.md), proving an exact isotropic quadratic moment and explicit quartic symbol error bound.
- **New entry:** [An Explicit Bound on the Relativistic Correction to Schrödinger Kinetic Energy](schrodinger-remainder-bound/index.md), proving the exact kinetic decomposition and a quartic correction bound.

## 2026-11-07

- **New entry:** [The Covering Radius of the Reed-Muller Code RM(5,9) Is 32](rm59-upper/index.md), proving $\rho(\mathrm{RM}(5,9))\le32$.

## 2026-11-04

- **Updated entry:** [A Square-Root Bound for Asymptotic Tensor Rank](tensor-rank/index.md), extending the bounds to arbitrary fields with a polynomial and cyclic proof.

## 2026-11-02

- **Licensing:** Entries may use Apache 2.0, so adapted formalizations can retain their upstream licensing.
- **New entry:** [Crossing Decomposition for Subquadratic Noncommutative Circuits](crossing-decomposition/index.md), giving circuits of size $O(n^{5/3})$ for symmetric noncommutative quartics over every field.

## 2026-11-01

- **New entry:** [A three-party Bell polytope that is not a cross-polytope](symmetric-bell-cross-polytope/index.md),
  giving the $(N,m)=(3,17)$ counterexample with at least nineteen distinct extreme points.

## 2026-10-27

- **New entry:** [MinRank Lower Bounds for the Cocubic Reed–Muller Covering Radius](cocubic-covering/index.md), reducing cocubic coset-weight lower bounds to affine MinRank and giving bounds of $32$, $32$, and $34$ in $9$, $10$, and $11$ variables.

## 2026-10-25

- **New entry:** [A quadratic ceiling for common-information bounds on spanning-tree slack matrices](spanning-tree-common-information/index.md),
  giving the explicit $4n^2$ ceiling for full canonical slack and for subtour rows.
- **New entry:** [Common information and hyperplane separation are incomparable](common-information-hsb/index.md),
  with exact separating families, finite conditional-independent seeds, and
  quantified failure of polynomial comparisons for the raw matrix functionals.

## 2026-10-23

- **New entry:** [Symmetric formulations of the spanning-tree polytope](spanning-tree-symmetric-ef/index.md),
  formalizing conditional Hamilton-path LP lower bounds, sharp LP approximations,
  exact quadratic-size SDP formulations, and a nonnegative-outer PSD lower bound.

## 2026-10-22

- **New entry:** [Distributional lower bounds for randomized linear-oracle optimization](distributional-linear-oracle-lower-bounds/index.md).

## 2026-10-21

- **New entry:** [A Square-Root Bound for Asymptotic Tensor Rank](tensor-rank/index.md).

## 2026-10-20

- **Identifiers now follow arXiv's format**, `lemmata:YYMM.NNNNN` (e.g. `lemmata:2610.00003`).
  Each entry has a landing page `/abs/YYMM.NNNNN` (abstract, status, citation) and the full
  entry at `/html/YYMM.NNNNN`. The identifiers issued earlier today in the
  `lemmata:2026.NNNNN` form were replaced.
- Entries can carry an **abstract**, shown on their landing page.
- The verification panel says **kernel-checked** and names the Lean version; the full
  definition moved to [What "checked" means](checked.md).
- Entries that no longer build after a Lean upgrade can be **frozen** by the maintainers:
  they stay published with the version and date of their last successful check.
- Every entry has a **stable identifier** with a permanent URL, shown at the top of the
  page and used in the citation.
- Machine-readable views for search engines and language models: `/llms.txt`,
  `/lemmata.json` (identifiers, Lean declarations, axioms, BibTeX) and a corrected
  `/sitemap.xml`.
- **Moved** to [github.com/ZIB-IOL/lemmata](https://github.com/ZIB-IOL/lemmata). Source and
  commit links on every page now point there.
- Entries can state an **AI use** note and **acknowledgements**, shown at the end of the page.
  First used on [Nonnegative rank of the spanning-tree slack matrix](spanning-tree-min-split/index.md).
- Entries can name their **contributors** explicitly, for the header line and the citation.
- The two minimal examples *Self-implication* and *Antisymmetry of order* were removed;
  [Composition of implications](implication-composition/index.md) remains as the worked example.

## 2026-10-19

- **New entry:** [A Lagrangian duality gap that survives closed convexification](lagrangian-duality-gap/index.md).
- **New entry:** [Nonnegative rank of the spanning-tree slack matrix](spanning-tree-min-split/index.md).
- Entries are grouped into **categories**; every page has a **Cite as** BibTeX entry.
- The archive went live at lemmata.iol.berlin.
