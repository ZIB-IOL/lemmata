---
numbering:
  headings: false
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
  `axiom`, and no computation (`native_decide`, see [below](#computation)), whose claims are
  evaluated by compiled code rather than checked by the kernel. This audit covers every
  declaration in the archive, not only the ones a page displays, so a result cannot hide an
  unproved helper.
- **It is bound to the prose.** The manifest names, for each numbered statement on the page,
  the Lean declaration that formalizes it; the tools check that the declaration exists, has
  the stated kind, and lives in the entry's own namespace.

The badge names the Lean version the result was checked with. A definition is marked
**◇ elaborated definition**: it compiled and was accepted, but a definition is not a claim.

The exact axioms each result depends on are recorded in the machine-readable index,
[`lemmata.json`](https://lemmata.iol.berlin/lemmata.json).

(computation)=
## Computation

Some facts are easiest to establish by running a program: checking finitely many cases, say.
Lean's `native_decide` does this by compiling a Boolean expression and running it during the
build; if it evaluates to `true`, the claim "this expression is `true`" is added as an
**axiom**. The kernel does not check that claim, and the archive does not re-run it, so a
result that depends on one is weaker than a kernel-checked result. Bugs in the compiler, in
the code it runs, or in any code that changes what the build compiles, could make a false
claim pass.

An entry may use computations only if its manifest declares `native_computation: true`, and
results that depend on one are marked apart from kernel-checked ones:

| Badge | Meaning |
|---|---|
| **✓ kernel-checked** | as above: no computation anywhere among its dependencies |
| **◐ kernel-checked, modulo computation** | its own proof is kernel-checked, but it uses results of *another* entry that rely on computations (that entry is linked) |
| **⚙ checked by computation** | it relies on a computation of its *own* entry |

Entry lists show both of the latter as **checked mod. computation**. The entry page lists
every computation its results rely on: the line of the Lean source that runs it, the claim as
written there, and the claim as the kernel stores it. The axiom audit still applies to
everything else: a computation is accepted only if it has exactly the form Lean's tactic
produces, comes from an entry that declared it, and was recorded at the exact place in the
source where `native_decide` (or `decide +native`, `bv_decide`) is called. Such an entry may
not define tactics, macros or syntax, run code while it is compiled, or import a module of
the archive that defines tactics, macros or syntax, so that, read from the source, each call
is Lean's own tactic. These rules check the source; they cannot prove what ran when it was
compiled, which is why such results carry the computation label in the first place. A hand-written `axiom`, `@[implemented_by]` or `@[extern]` is
refused everywhere.

Whoever runs `tools/check.sh` on the repository re-runs every computation on their own
machine, which is how a reviewer checks them. Where a proof by `decide +kernel` is feasible,
it is preferred: the kernel then evaluates the claim itself, and the result stays
kernel-checked.

## What it does not mean

The badge does **not** say that the English statement means the same as the Lean statement.
That correspondence is checked by human review. Every entry links to the exact formal source,
at the exact commit, that it was reviewed against, so a reader can compare the two.

Nor does it say that the proof written in the prose is the one Lean checked. Only the
statements are bound to the prose; the Lean proof may take another route, for instance with
stronger intermediate estimates.

It is also independent of Lean's own warnings, which a `set_option` can switch off: the axiom
audit reads what each compiled proof actually depends on.

It rests on Lean's kernel being correct. Kernel bugs are rare and fixed quickly, but they
happen: in July 2026 a bug in the handling of nested inductive types let a false proof
through ([lean4#14576](https://github.com/leanprover/lean4/issues/14576), fixed within an
hour). Every result here was checked with a Lean release that contains the fix, and the
badge names the version used.

It also does not say anything about novelty, priority, or the importance of a result.

For a fuller account of what to check before trusting "verified in Lean", and why it is
never only about certification, see @spiegel2026trust.

## How the check runs

Contributions are pull requests against the archive's Git repository. After a merge, the
site's build compiles the whole library, runs the kernel check and the axiom audit, and
publishes the new version only if every check passes. A commit that fails leaves the previous
version online; the [build status](https://lemmata.iol.berlin/_status) says why.
