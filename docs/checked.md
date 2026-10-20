---
title: What "checked" means
---

Every formal result in the archive carries a status badge. This page says exactly what
that badge establishes, and what it does not.

## Kernel-checked

A result marked **✓ kernel-checked (Lean v…)** satisfies all of the following, established
by machinery rather than by the author:

- **It compiles.** The Lean declaration exists in the archive's library and builds with the
  pinned Lean and Mathlib versions [@mathlib2020].
- **Lean's kernel accepted it.** The kernel re-checks every declaration of the archive from
  the compiled files (`leanchecker`), independently of the elaborator that produced them.
- **It uses only the standard axioms.** The result depends on no axioms beyond `propext`,
  `Classical.choice` and `Quot.sound`. In particular it contains no `sorry`, no custom
  `axiom`, and no `native_decide`, whose proofs are evaluated by compiled code rather than
  checked by the kernel. This audit covers every declaration in the archive, not only the
  ones a page displays, so a result cannot hide an unproved helper.
- **It is bound to the prose.** The manifest names, for each numbered statement on the page,
  the Lean declaration that formalizes it; the tools check that the declaration exists, has
  the stated kind, and lives in the entry's own namespace.

The badge names the Lean version the result was checked with. A definition is marked
**◇ elaborated definition**: it compiled and was accepted, but a definition is not a claim.

The exact axioms each result depends on are recorded in the machine-readable index,
[`lemmata.json`](https://lemmata.iol.berlin/lemmata.json).

## What it does not mean

The badge does **not** say that the English statement means the same as the Lean statement.
That correspondence is checked by human review. Every entry links to the exact formal source,
at the exact commit, that it was reviewed against, so a reader can compare the two.

It also does not say anything about novelty, priority, or the importance of a result.

## How the check runs

Contributions are pull requests against the archive's Git repository. After a merge, the
site's build compiles the whole library, runs the kernel check and the axiom audit, and
publishes the new version only if every check passes. A commit that fails leaves the previous
version online; the [build status](https://lemmata.iol.berlin/_status) says why.
