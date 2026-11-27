# Lemmata

A living archive of mathematics at **<https://lemmata.iol.berlin>**. Every entry is written
twice — as prose for people (MyST Markdown, rendered with KaTeX, numbered results,
cross-references, Mermaid and small JavaScript widgets) and as a Lean 4 formalization on
top of Mathlib that the kernel has checked.

```
docs/categories.yml            the categories, in sidebar order
docs/<id>/                     prose: contribution.yml + index.md (+ more pages, figures, widgets)
lean/Lemmata/<LeanName>/       formal: Main.lean (+ more modules), one shared Lake package
lean/Lemmata/Shared/           helpers used by more than one entry
checker/                       lemmata-check and lemmata-replay, the trusted verifier (see below)
tools/lemmata.mjs              validate / umbrella / prepare / new
tools/check.sh                 the full pipeline, locally (or only what a change affects)
```

## How publishing works

There is no CI. The cluster watches **`main`**: on every new commit it builds the Lean
library, re-checks it in the kernel, audits the axioms, renders the site and switches the
site to the new version only if every step passed. A failed commit leaves the previous
version online and shows the reason on the status page. Merging to `main` is publishing,
so `main` is protected and changes arrive through pull requests.

| Step | What it guarantees |
|---|---|
| `validate` | every `docs/<id>/` has its `lean/Lemmata/<Name>/` and vice versa; manifests, labels, snippet markers and the umbrella are consistent |
| `lake build` | every module under `lean/Lemmata/` compiles — including files nothing imports |
| `lemmata-replay` | the kernel re-checks every declaration of our modules from the compiled files |
| `lemmata-check` | **no declaration anywhere in the archive** uses an axiom beyond `propext`, `Classical.choice`, `Quot.sound` (so no `sorry` and no custom axioms; computations only in an entry that declares `native_computation: true`); every public declaration lies in its entry's namespace; every exported declaration exists and has the declared kind |
| `myst build` | the site builds with unresolved references treated as errors |

The verification panel on each page is generated from `lemmata-check`'s report. Nothing a
contributor writes can produce a "checked" badge.

**What "checked" does not mean:** that the English statement and the Lean statement say
the same thing. That is what review is for; the page links the exact formal source, at the
exact commit, that it was reviewed against.

## Working locally

Requirements: [elan](https://github.com/leanprover/elan) and Node ≥ 24.

```bash
npm ci                       # mystmd + the browser-test tool, pinned
tools/check.sh               # everything the cluster does; first run downloads Mathlib's cache (~7 GB)
tools/check.sh --changed     # only the entries your branch changes, and the entries that import them
tools/check.sh --entry <id>  # only that entry, and the entries that import it
tools/check.sh --no-docs     # stop after the axiom audit (combines with the two above)
npm run preview              # live-reloading site at http://localhost:3000 (no verification)
node tests/browser.mjs docs/_build/html ""   # browser smoke test of the rendered site
```

See [CONTRIBUTING.md](CONTRIBUTING.md) to add an entry. **Agents:** follow
[AGENTS.md](AGENTS.md), the complete step-by-step procedure from clone to a confirmed
publication.

## The verifier

`checker/` is a separate Lake project with no dependencies besides Lean itself. It loads
the compiled archive without running any of its code (`loadExts := false`) and computes
axiom dependencies by walking kernel terms itself, rather than trusting the axiom tables
stored in the build output. `lemmata-replay` sends every declaration of the archive through
Lean's kernel again, in one pass over all modules with Mathlib loaded once. The cluster runs
**its own copy** of this checker, maintained in the deployment repository, so editing
`checker/` here cannot loosen what `main` is held to.

A partial check (`--changed`, `--entry`) builds what its entries import from other entries
but re-checks and audits only their own modules: the rest is unchanged, and the cluster
checks every entry on every commit. Because every public declaration must lie in its
entry's namespace, two entries can never clash, so the partial check is equivalent to the
full one for the entries it covers. It switches to the full check by itself when a change
can affect every entry (the Lake configuration, the toolchain, `checker/`, `tools/`).

Pinned: Lean `v4.35.0`, Mathlib `v4.35.0`, mystmd `1.11.0`, book theme
`23f2df5493e23dfb1d9433c8aa64c87beb4232a3`.
