# Contributing an entry

(Agents: [AGENTS.md](AGENTS.md) is the same procedure as an exact checklist, including
how to confirm publication.)

An entry is a pair: a page in `docs/<id>/` and a Lean module in `lean/Lemmata/<LeanName>/`.

## 1. Scaffold

```bash
node tools/lemmata.mjs new prime-infinitude PrimeInfinitude number-theory
```

The last argument is the entry's category, one of the ids in `docs/categories.yml`. If
your entry needs a category that does not exist yet, add it to that file in the same
pull request (id, title, one-line description); its position in the file is its position
in the sidebar.

This creates `docs/prime-infinitude/{contribution.yml,index.md}` and
`lean/Lemmata/PrimeInfinitude/Main.lean`, and adds the module to the umbrella. The id is
lowercase kebab-case and becomes the URL (`/prime-infinitude/`); the Lean name is
UpperCamelCase. Neither can change after publication. Some ids are reserved because they are
site paths: `abs`, `html`, `c`, `changelog`, `checked`, `llms`, `index`, and anything starting
with `_`; the Lean name `Shared` is reserved for helpers used by several entries.

## 2. Write the Lean

- Start files with `module` and use `public import` (Mathlib uses the module system).
- Everything lives in `namespace Lemmata.<LeanName>`.
- Import other entries' modules directly (`public import Lemmata.ImplicationComposition.Main`),
  never the umbrella `Lemmata`. Do not copy another entry's definitions; move shared
  material into `lean/Lemmata/Shared/` in its own pull request.
- No `sorry`, no `native_decide`, no `axiom`. The audit covers every declaration in
  every file, not just the ones you export — a draft helper fails the whole archive.
- Mark the part to show on the page with `-- DOCS_BEGIN_MAIN` / `-- DOCS_END_MAIN`.
  Each marker must occur exactly once.

### Separate statements from proofs (recommended)

Put the **definitions and formal statements** in one module and the **proofs** in another,
so the statement never depends on the proof — only the proof on the statement. This is what
[Lax](https://laxarchive.org/about.html) (`concepts/` vs `proofs/`) and DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) do, and it is
what a reader reviews: the statement is the claim, the proof is the evidence.

```
lean/Lemmata/<LeanName>/
  Statement.lean   definitions and the theorem statements, as `def … : Prop := …`
  Main.lean        `public import Lemmata.<LeanName>.Statement`; the proofs
```

In `Statement.lean`, state the claim as a proposition:

```lean
/-- Composition of implications. -/
def Composition : Prop := ∀ {P Q R : Prop}, (P → Q) → (Q → R) → P → R
```

and in `Main.lean` prove exactly that proposition, and export this theorem:

```lean
theorem composition : Composition := fun hpq hqr hp => hqr (hpq hp)
```

Then the statement a reviewer compares with the prose is short and proof-free, and a
proof can be replaced later without touching what was claimed. This is not enforced —
small entries may keep everything in `Main.lean` — but new entries should follow it.

## 3. Write the page

- State results with `prf:theorem` (or `prf:lemma`, `prf:definition`, …) and give each a
  `:label:` containing your id, e.g. `thm-prime-infinitude`.
- Include the Lean with `literalinclude` from `../../lean/...`. Never paste a proof by hand.
- Write each informal proof as ```` ```{prf:proof} of [](#thm-<id>) ```` with `:nonumber:` on
  the next line, so it reads "Proof (of Theorem 1)" instead of a bare "Proof 1".
  Validation enforces this.
- Refer to other entries' results by label: `[](#thm-implication-composition)`.
- Keep both generated includes the scaffold writes: `../_generated/provenance/<id>.md`
  under the title (who contributed, from git — your name is your git author name) and
  `../_generated/verification/<id>.md` at the end (what was checked). Validation requires
  both. Do not add an `authors:` block; the git line replaces it.
- Widgets: an ES module next to the page, loaded with `{anywidget}`. Use only
  `model.get`, `model.set` and `model.on` — there is no kernel. Widgets run in readers'
  browsers and are reviewed as code.

## 4. Bind them in `contribution.yml`

```yaml
schema_version: 1
id: prime-infinitude
lean_namespace: Lemmata.PrimeInfinitude
category: number-theory      # where it sits in the sidebar (docs/categories.yml)
tags: [logic]                # optional: also listed on these categories' pages
arxiv: 2301.01234            # optional: linked under the title; one id or a list
abstract: >-                 # optional: one paragraph, shown on the /abs/ landing page
  ...
contributors:                # optional: credit these people instead of the git authors
  - Ada Lovelace
  - {first: Ludwig, last: van Beethoven}   # multi-part surname
ai_use: >-                   # optional: how AI tools were used (end of the page)
  ...
acknowledgements: >-         # optional: funding, thanks (end of the page); $math$ allowed
  ...
pages: [index.md]            # first page must be index.md; list every page
exports:
  - name: Lemmata.PrimeInfinitude.exists_infinite_primes
    kind: theorem            # or: definition
    page: index.md
    label: thm-prime-infinitude
```

Rules the tools enforce for these fields:

- `category` must be an id in `docs/categories.yml`; `tags` are further category ids and may
  not repeat the primary category.
- `arxiv` is the bare identifier (`2301.01234`, `2301.01234v2`, `math/0601001`), without an
  `arXiv:` prefix; the format is checked so a typo cannot become a dead link.
- `abstract`, `ai_use` and `acknowledgements` are inline text only: words, `*emphasis*`,
  `[links](…)` and math `$…$` / `$$…$$`. No directives, code fences, headings, lists or HTML;
  write a literal dollar as `\$`; at most 2000 characters each. Use a YAML block (`>-`).
- `contributors` items are `First Last` or `{first: …, last: …}`; names only, no emails.

The URL of an entry is `/<id>/` and does not contain its category, so recategorising an
entry later never breaks links to it. Category pages live at `/c/<category>/`.

Each export says "this label on this page is formalized by this declaration". The binding
is checked; whether the two say the same thing is what your reviewer checks.

## 5. Check and open a pull request

Do not run `lake update`: the dependency set in `lean/lake-manifest.json` is pinned, and the
build rejects a commit whose manifest differs. Never commit `.lemmata/`, `docs/_generated/`,
`docs/c/`, `docs/abs/` or build output (they are git-ignored). Commit with your GitHub noreply
address (`git config user.email <id>+<user>@users.noreply.github.com`): GitHub refuses pushes
that expose a private email, and `user.name` is the name shown on the page.


```bash
node tools/lemmata.mjs umbrella --write   # if you added or removed Lean files
tools/check.sh
```

Open a pull request against `main` on [GitHub](https://github.com/ZIB-IOL/lemmata). If
the change matters to readers (a new entry, a correction), add a line to
`docs/changelog.md` in the same pull request. Reviewers read the mathematics, compare the prose
with the Lean statement, and review any JavaScript. Once merged, the entry is live within
a few minutes, or the status page says why not.

## Identifiers, later changes, and Lean upgrades

On first publication an entry gets a stable identifier `lemmata:YYMM.NNNNN` with a landing
page `/abs/YYMM.NNNNN` and the full entry at `/html/YYMM.NNNNN`; cite that. To change an entry
later, open another pull request on the same directories — the identifier stays.

The archive builds with one Lean and Mathlib version. If an upgrade breaks an entry, the
maintainers may **freeze** it: it stays published, marked with the Lean version and date of
its last successful check, and is left out of later builds while its files are unchanged. To
bring it back, port it to the current version and ask for it to be unfrozen.
