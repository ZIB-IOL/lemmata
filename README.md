# Lemmata

A living archive of mathematics at **<https://lemmata.iol.berlin>**. Every entry is written
twice — as prose for people (MyST Markdown, rendered with KaTeX, numbered results,
cross-references, Mermaid and small JavaScript widgets) and as a Lean 4 formalization on
top of Mathlib that the kernel has checked.

```
docs/<id>/                     prose: contribution.yml + index.md (+ more pages, figures, widgets)
lean/Lemmata/<LeanName>/       formal: Main.lean (+ more modules), one shared Lake package
lean/Lemmata/Shared/           helpers used by more than one entry
checker/                       lemmata-check, the trusted verifier (see below)
tools/lemmata.mjs              validate / umbrella / prepare / new
tools/check.sh                 the full pipeline, locally
```

## How publishing works

There is no CI. The cluster watches **`main`**: on every new commit it builds the Lean
library, re-checks it in the kernel, audits the axioms, renders the site and switches the
site to the new version only if every step passed. A failed commit leaves the previous
version online and shows the reason on the status page. Merging to `main` is publishing,
so `main` is protected and changes arrive through merge requests.

| Step | What it guarantees |
|---|---|
| `validate` | every `docs/<id>/` has its `lean/Lemmata/<Name>/` and vice versa; manifests, labels, snippet markers and the umbrella are consistent |
| `lake build` | every module under `lean/Lemmata/` compiles — including files nothing imports |
| `leanchecker` | the kernel re-checks every declaration of our modules from the compiled files |
| `lemmata-check` | **no declaration anywhere in the archive** uses an axiom beyond `propext`, `Classical.choice`, `Quot.sound` (so no `sorry`, no `native_decide`, no custom axioms); every exported declaration exists, has the declared kind, and lives in its entry's namespace |
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
tools/check.sh --no-docs     # stop after the axiom audit
npm run preview              # live-reloading site at http://localhost:3000 (no verification)
node tests/browser.mjs docs/_build/html ""   # browser smoke test of the rendered site
```

See [CONTRIBUTING.md](CONTRIBUTING.md) to add an entry.

## The verifier

`checker/` is a separate Lake project with no dependencies besides Lean itself. It loads
the compiled archive without running any of its code (`loadExts := false`) and computes
axiom dependencies by walking kernel terms itself, rather than trusting the axiom tables
stored in the build output. The cluster runs **its own copy** of this checker, maintained
in the deployment repository, so editing `checker/` here cannot loosen what `main` is held to.

Pinned: Lean `v4.35.0`, Mathlib `v4.35.0`, mystmd `1.11.0`, book theme
`23f2df5493e23dfb1d9433c8aa64c87beb4232a3`.
