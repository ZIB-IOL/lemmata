# Contributing an entry

An entry is a pair: a page in `docs/<id>/` and a Lean module in `lean/Lemmata/<LeanName>/`.

## 1. Scaffold

```bash
node tools/lemmata.mjs new prime-infinitude PrimeInfinitude
```

This creates `docs/prime-infinitude/{contribution.yml,index.md}` and
`lean/Lemmata/PrimeInfinitude/Main.lean`, and adds the module to the umbrella. The id is
lowercase kebab-case and becomes the URL (`/prime-infinitude/`); the Lean name is
UpperCamelCase. Neither can change after publication.

## 2. Write the Lean

- Start files with `module` and use `public import` (Mathlib uses the module system).
- Everything lives in `namespace Lemmata.<LeanName>`.
- Import other entries' modules directly (`public import Lemmata.SelfImplication.Main`),
  never the umbrella `Lemmata`. Do not copy another entry's definitions; move shared
  material into `lean/Lemmata/Shared/` in its own merge request.
- No `sorry`, no `native_decide`, no `axiom`. The audit covers every declaration in
  every file, not just the ones you export — a draft helper fails the whole archive.
- Mark the part to show on the page with `-- DOCS_BEGIN_MAIN` / `-- DOCS_END_MAIN`.
  Each marker must occur exactly once.

## 3. Write the page

- State results with `prf:theorem` (or `prf:lemma`, `prf:definition`, …) and give each a
  `:label:` containing your id, e.g. `thm-prime-infinitude`.
- Include the Lean with `literalinclude` from `../../lean/...`. Never paste a proof by hand.
- Refer to other entries' results by label: `[](#thm-self-implication)`.
- Keep the `{include} ../_generated/verification/<id>.md` line: that is the verification panel.
- Widgets: an ES module next to the page, loaded with `{anywidget}`. Use only
  `model.get`, `model.set` and `model.on` — there is no kernel. Widgets run in readers'
  browsers and are reviewed as code.

## 4. Bind them in `contribution.yml`

```yaml
schema_version: 1
id: prime-infinitude
lean_namespace: Lemmata.PrimeInfinitude
pages: [index.md]            # first page must be index.md; list every page
exports:
  - name: Lemmata.PrimeInfinitude.exists_infinite_primes
    kind: theorem            # or: definition
    page: index.md
    label: thm-prime-infinitude
```

Each export says "this label on this page is formalized by this declaration". The binding
is checked; whether the two say the same thing is what your reviewer checks.

## 5. Check and open a merge request

```bash
node tools/lemmata.mjs umbrella --write   # if you added or removed Lean files
tools/check.sh
```

Open a merge request against `main`. Reviewers read the mathematics, compare the prose
with the Lean statement, and review any JavaScript. Once merged, the entry is live within
a few minutes, or the status page says why not.
