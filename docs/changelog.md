---
numbering:
  headings: false
title: Changelog
---

What changed in the archive that a reader should know about: new entries, corrections to
published entries, and changes to what "checked" means. Routine edits are not listed; every
entry shows its own last change and links to the exact commit.

Newest first. Add an item in the same pull request as the change it describes.

## 2026-11-26

- **Updated entry:** [Conditional gradient methods: away-step and fully-corrective Frank–Wolfe](away-step-frank-wolfe/index.md), completing Proposition 2.31: the pyramidal width equals the facial distance, in every finite-dimensional real normed space.
- **Updated entry:** [Conditional gradient methods: away-step and fully-corrective Frank–Wolfe](away-step-frank-wolfe/index.md), adding Proposition 2.31's lower bound: the facial distance is a scaling constant, so the linear rates hold with it.
- **Updated entry:** [Frank–Wolfe: the core](frank-wolfe-core/index.md), adding polyhedral tools for later entries: closedness of finitely generated cones, the Farkas lemma, and exposed and minimal faces of polytopes.
- **New entry:** [Conditional gradient methods: away-step and fully-corrective Frank–Wolfe](away-step-frank-wolfe/index.md), proving that the away-step and fully-corrective Frank–Wolfe algorithms converge linearly over polytopes for smooth strongly convex objectives, with rates governed by the pyramidal width.
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
