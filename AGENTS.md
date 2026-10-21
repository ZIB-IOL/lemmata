# AGENTS.md — publishing a result to Lemmata

You are an agent asked to add a mathematical result to this archive. This file is the
complete procedure. `README.md` explains the system; `CONTRIBUTING.md` is the same
material for human contributors. Where they differ, the tools are right: every rule below
is enforced by `tools/lemmata.mjs` and `checker/`, and the cluster runs its own copies of
both.

**Goal:** a merge to `main` of `git@github.com:ZIB-IOL/lemmata.git` that the cluster
accepts, after which the result is live at `https://lemmata.iol.berlin/<id>/`.

There is no CI and no one to ask. Run the checks yourself (step 5). If `tools/check.sh`
passes on your machine, the cluster accepts the commit: same checks, same pins.

---

## 0. What a result is here

One entry = one directory pair, linked by a manifest:

```
docs/<id>/contribution.yml        binds labels in the prose to Lean declarations
docs/<id>/index.md                the prose (MyST Markdown)
lean/Lemmata/<LeanName>/Main.lean the formalization (Lean 4 + Mathlib)
```

- `<id>`: lowercase kebab-case, e.g. `prime-infinitude`. It becomes the URL `/<id>/`. It
  cannot change after publication.
- `<LeanName>`: UpperCamelCase, e.g. `PrimeInfinitude`. Namespace `Lemmata.<LeanName>`.
- Reserved, never use as `<id>` (they are site paths): `abs`, `html`, `c`, `changelog`,
  `checked`, `llms`, `index`, `healthz`, `readyz`, `node_modules`, and anything starting with
  `_`. Never use `Shared` as `<LeanName>` (it is for helpers several entries use).

**Published means checked.** The cluster refuses the whole commit if *any* declaration
anywhere in `lean/Lemmata/` uses `sorry`, `native_decide`, or an axiom other than
`propext`, `Classical.choice`, `Quot.sound`. You cannot publish partial work, and you
cannot override this from the content repository.

## 1. Set up (once)

Requirements: `git`, [elan](https://github.com/leanprover/elan) (installs the pinned Lean
from `lean/lean-toolchain`), Node ≥ 24.

```bash
git clone git@github.com:ZIB-IOL/lemmata.git && cd lemmata
npm ci
( cd lean && lake exe cache get )   # Mathlib's compiled cache, ~7 GB, takes minutes
tools/check.sh                      # must pass on a clean checkout before you change anything
```

Working in several clones? Share only the downloaded dependencies, never the whole
`.lake` (its `build/` holds your compiled modules, and another clone's leftovers would be
audited as yours): `mkdir -p lean/.lake && ln -s /path/to/first/clone/lean/.lake/packages
lean/.lake/packages`.

Never run `lake update`. The dependency set in `lean/lake-manifest.json` is pinned, and the
cluster rejects any commit whose manifest differs from its cache in any package.

## 2. Create the entry

```bash
git checkout -b entry/<id>
node tools/lemmata.mjs new <id> <LeanName> <category>
```

`<category>` must be an `id` from `docs/categories.yml`. If no category fits, add one to
that file in the same branch:

```yaml
- id: number-theory              # lowercase kebab-case
  title: Number theory
  description: One sentence.     # shown on the landing page and the category page
```

The scaffold writes all three files with placeholders and registers the module in
`lean/Lemmata.lean`. Replace every placeholder; the placeholder theorem `main : True`
must not survive.

## 3. Write the Lean

`lean/Lemmata/<LeanName>/Main.lean`:

```lean
module

public import Mathlib.Order.Basic            -- import only what you use

public section

namespace Lemmata.<LeanName>

-- DOCS_BEGIN_MAIN
/-- Docstring: what the theorem says, in words. -/
theorem my_result (n : ℕ) : n + 0 = n := by simp
-- DOCS_END_MAIN

end Lemmata.<LeanName>
```

Rules (each enforced):

- First line `module`, imports as `public import`, body in `public section`. Mathlib at
  this pin uses the module system; plain `import` produces warnings and missing modules.
- Module names must exist at the pinned Mathlib. Check with
  `ls lean/.lake/packages/mathlib/Mathlib/...` rather than from memory: for example,
  `Mathlib.Logic.Basic` does **not** exist at this pin.
- Everything inside `namespace Lemmata.<LeanName>`.
- To use another entry, `public import Lemmata.<Other>.Main`. **Never** import the umbrella
  `Lemmata`, and never copy another entry's definitions.
- `-- DOCS_BEGIN_MAIN` and `-- DOCS_END_MAIN` occur exactly once each, in that order. The
  page shows exactly what is between them.
- Exported declarations are public (not `private`), live in this namespace, and are defined
  in this directory's modules.
- More files are fine (`lean/Lemmata/<LeanName>/Lemmas.lean`, …). After adding or removing
  any `.lean` file run `node tools/lemmata.mjs umbrella --write`. Every file is compiled and
  audited, including files nothing imports.

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

Fast loop while proving:

```bash
tools/check.sh --no-docs    # build + kernel check + axiom audit, no site render
```

## 4. Write the prose and bind it

`docs/<id>/index.md`:

````markdown
---
title: A short human title
---

```{include} ../_generated/provenance/<id>.md
```

One or two sentences of context.

```{prf:theorem} Name of the result
:label: thm-<id>

The statement in mathematical language, with $\LaTeX$ math.
```

```{prf:proof} of [](#thm-<id>)
:nonumber:

The informal proof.
```

```{literalinclude} ../../lean/Lemmata/<LeanName>/Main.lean
:language: lean
:start-after: -- DOCS_BEGIN_MAIN
:end-before: -- DOCS_END_MAIN
```

```{include} ../_generated/verification/<id>.md
```
````

- Keep both `{include}` lines; validation fails without them. The first renders the
  header under the title: the identifier with "copy URL" and "copy BibTeX", the authors
  (computed by the cluster from git history, names only, each linked to an author page at
  `/a/<name>/`), the versions (`v1 <date> · last <date>`, linked to the commit) and the
  abstract. The last is the verification panel, from the verifier's report, collapsed with
  its outcome in the bar, followed by related material, notes and the license. Neither can
  be edited: do not add an `authors:` block, and never write "checked", "verified" or a
  badge yourself.
- The BibTeX (permanent `/abs/` URL, authors, year, arXiv if given, the version commit in
  `note`) is generated; there is nothing to write.
- On the built site (`tools/check.sh`, and in the cluster) proof titles read "Proof of
  Theorem 1", a result whose proof is not directly below it gets a `[↓]` link to it, proofs
  fold by clicking their header, and the Lean source starts collapsed. A small script does
  this in the browser; `npm run preview` (MyST's live server) does not run it.
- Your name on the page is the **git author name** of your commits, unless the manifest
  lists `contributors` (step 4). Set it before committing: `git config user.name "Full Name"`.
- Every `prf:proof` names what it proves and carries `:nonumber:`, exactly as above;
  it renders as "Proof (of Theorem 1)" with a link. Validation fails otherwise: MyST
  numbers proofs on their own, so a page with a theorem, a proposition and one proof
  would say "Proof 1" and leave the reader guessing. A proof of several statements
  lists them all: `of [](#prop-<id>-…) and [](#thm-<id>)`.
- **DOI links need a BibTeX entry.** MyST turns every `https://doi.org/…` (or `doi:…`)
  link into a citation and looks it up online while rendering; the cluster renders
  **without internet**, so the lookup fails there and the entry is not published. After
  adding a DOI link, run `node tools/lemmata.mjs doi`: it fetches the entry from doi.org
  into `docs/references.bib`. Commit that file too. `validate` refuses a linked DOI that is
  not in `references.bib`, and `tools/check.sh` also renders offline to catch anything
  else that would need the network. Tidy the fetched entry if you like (doi.org's titles
  can contain HTML such as `<i>b</i>`; write `$b$`); keep its `doi` field.
- Never paste Lean into Markdown by hand; always `literalinclude`.
- Refer to results by label: `[](#thm-implication-composition)`. Labels from other entries work.
- Other environments: `prf:lemma`, `prf:definition`, `prf:corollary`, `prf:proposition`.
  Display equations: `$$ … $$ (eq-<id>-name)`.
- Every page in `docs/<id>/` must be listed in `pages:` below, `index.md` first.

`docs/<id>/contribution.yml`:

```yaml
schema_version: 1
id: <id>                              # = directory name
lean_namespace: Lemmata.<LeanName>
category: <category>                  # an id from docs/categories.yml
tags: [<other-category>]              # optional; never the primary category
arxiv: 2301.01234                     # optional; one id or a list, e.g. [2301.01234v2, math/0601001]
abstract: >-                          # REQUIRED; under the header and on the /abs/ page
  One paragraph stating the result; inline text and $math$ only.
contributors:                         # optional; replaces the names taken from git
  - Ada Lovelace                      #   "First Last"
  - {first: Ludwig, last: van Beethoven}   # surnames with several parts
ai_use: >-                            # optional; shown at the end of the entry
  Lean proofs drafted with an AI assistant, reviewed and completed by the authors.
acknowledgements: >-                  # optional; shown at the end of the entry
  Supported by the Berlin Mathematics Research Center MATH$^+$.
license: CC-BY-4.0                    # optional; CC-BY-4.0 (default), CC-BY-SA-4.0 or CC0-1.0
withdrawn: >-                         # only to withdraw a published entry; the reason
  The bound in the second theorem is wrong; see lemmata:2611.00004 for the correction.
related:                              # optional; derived material, listed at the end
  - {kind: slides, title: "Talk at the MATH+ day", url: "https://example.org/slides.pdf"}
  - {kind: video,  title: "Recording", url: "https://example.org/video"}
pages:
  - index.md
exports:                              # at least one theorem
  - name: Lemmata.<LeanName>.my_result
    kind: theorem                     # or: definition
    page: index.md
    label: thm-<id>                   # must contain <id>; must occur exactly once on that page
```

`contributors` is for when the git authors are not the right credit: several people
wrote the result, someone committed on behalf of others, or an agent did the commit.
If present, it replaces the git names in the contributors line and in the BibTeX
`author` field, in the order given; the dates and commit link still come from git.
Write `First Last`, or `{first: …, last: …}` when the surname has several parts (it is
then kept whole in BibTeX: `{van Beethoven}, Ludwig`). Names only — no emails.

`license` is the licence of the whole entry, prose and Lean, shown under the title and in
`lemmata.json`. Leave it out for **CC BY 4.0**, the default; `CC-BY-SA-4.0` and `CC0-1.0`
are the only alternatives, and anything else fails validation. Do not contribute text or
code you cannot license this way, e.g. passages copied from a paper whose publisher holds
the copyright; ask the human you work for when unsure.

`withdrawn` withdraws a published entry; its text is the reason. **Never delete a published
entry**: its identifier is cited, and other entries may import its Lean. A withdrawn entry
stays at its identifier with a notice under the title and keeps being built and checked, but
leaves the sidebar, the catalog and the category pages (`lemmata.json` gives it status
`withdrawn`). Correct mistakes by changing the entry instead, where you can. Withdraw only
when the human you work for asks you to; see the About page for the policy.

`ai_use` and `acknowledgements` are short notes rendered at the end of the entry, below the
verification panel. Say honestly how AI tools were used, if at all; there is no default
text. Both are inline only: text, `*emphasis*`, `[links](...)` and math `$...$` /
`$$...$$` (rendered by KaTeX). Directives, code fences, headings, lists and HTML are
refused, a literal dollar must be written `\$`, and each note is at most 2000 characters.
Use a YAML block (`>-`) so math and apostrophes need no quoting.

`arxiv` links additional material (a paper, a longer write-up) under the title as
`arXiv:<id>` → `https://arxiv.org/abs/<id>`. Give the bare identifier, without an
`arXiv:` prefix; validation checks the format, so a typo fails instead of becoming a
dead link. Unquoted is fine (`2301.10230` keeps its trailing zero).

Each export binds one label in the prose to one Lean declaration. The tools check that the
declaration exists, has that kind, lives in your namespace, and depends only on allowed
axioms. **Nobody can check that the English statement means the same as the Lean
statement.** That is your job, and your reviewer's: state the Lean theorem so that it
visibly says what the prose says, without extra hypotheses the prose omits.

## 5. Check (mandatory)

```bash
tools/check.sh
node tests/browser.mjs docs/_build/html ""    # follows every link; needs: npx playwright install chromium
```

`tools/check.sh` runs, in order and stopping at the first failure:

| Step | Fails when |
|---|---|
| validate | a manifest or category is wrong, a note uses non-inline markup, a label is missing or duplicated, snippet markers are wrong, the umbrella is stale, an `index.md` lacks one of the two `{include}` lines, `.lemmata/` is committed |
| lake build | any module does not compile |
| leanchecker | the kernel rejects a declaration |
| lemmata-check | any declaration uses a disallowed axiom (`sorryAx`, `native_decide`'s auxiliary axioms, custom `axiom`), or an export is missing, misclassified, or outside its namespace |
| myst build | a reference does not resolve, an identifier is duplicated, a linked file is missing |

Every failure is printed as `FAIL …` with the file and the reason. Fix the cause. Never
weaken a check, never edit `checker/` or `tools/` to get past one (the cluster ignores
your copies anyway), and never commit `docs/_generated/`, `docs/c/`, `docs/_build/`,
`docs/myst.runtime.yml`, `lean/.lake/` or `out/` (they are git-ignored).

## 6. Submit

**Commit with a public email.** GitHub refuses a push whose commits carry an email the
account keeps private ("push declined due to email privacy restrictions"). Use the account's
noreply address — `git config user.email <id>+<user>@users.noreply.github.com` — before you
commit; the name you set (`user.name`) is the one shown on the page.

```bash
git add -A
git commit -m "<id>: <one line on what is proved>"
git push -u origin entry/<id>
```

Open a pull request against `main` at `https://github.com/ZIB-IOL/lemmata/pulls`
and say what the result is and how the Lean statement corresponds to the prose. **Merging
is publishing**: a human reviews and merges. Do not push to `main` yourself unless you have
been explicitly told to.

## Identifiers and later changes

On its first publication every entry gets a **stable identifier**, `lemmata:YYMM.NNNNN`
(like arXiv), with a landing page `https://lemmata.iol.berlin/abs/YYMM.NNNNN` and the full
entry at `/html/YYMM.NNNNN`. The cluster assigns it;
you do not write it anywhere. It is shown at the top of the page and used as the BibTeX key
and URL. Link to and cite that URL, not the directory-based one.

To change an entry later, open another pull request against the same `docs/<id>/` and
`lean/Lemmata/<LeanName>/`. The identifier stays the same. The header's "last changed"
line and commit link update by themselves; the BibTeX `note` names the commit
of each published version, so earlier citations stay exact. Note substantive corrections
in `docs/changelog.md`.

### After a Lean or Mathlib upgrade

The archive builds with one Lean and Mathlib version. When an upgrade breaks an entry, the
maintainers may **freeze** it: it stays published, marked "last checked with Lean v… on …",
and its Lean code is left out of later builds. A frozen entry can only be shown with its old
result while its files are unchanged. To bring it back, port it to the current version in a
pull request and ask for it to be unfrozen; once it passes, it is current again.

## 7. Confirm it is live

After the merge, the cluster builds the new `main` within about a minute; a build takes
under a minute more. Poll the public status:

```bash
curl -s https://lemmata.iol.berlin/_status.json \
  | jq '{published: .active.sha, main: .head, stale, building, last: .last_attempt.result}'
```

- **Published** when `.active.sha` equals the merged commit (`git rev-parse origin/main`)
  and `.stale` is `false`. Your entry is at `https://lemmata.iol.berlin/<id>/`.
- **Rejected** when `.last_attempt.result` is `"failed"` for that commit.
  `.last_attempt.reason` names the failed step (`fetch`, `build`, `verify`, `render`,
  `upload`) and carries the end of its log. The site stays on the previous version. Fix it
  on a new branch and go back to step 5. Human-readable view: `https://lemmata.iol.berlin/_status`.
- Still `building`, or `waiting-for-mathlib-cache`: poll again in 30 s.

A commit that passed `tools/check.sh` locally and fails in the cluster is a bug in the
system, not in your entry. Report the status output to whoever asked for the work.

---

## Quick reference

```bash
node tools/lemmata.mjs new <id> <LeanName> <category>   # scaffold
node tools/lemmata.mjs umbrella --write                 # after adding/removing .lean files
node tools/lemmata.mjs validate                         # structure only, seconds
tools/check.sh --no-docs                                # + build, kernel, axioms
tools/check.sh                                          # everything the cluster does
npm run preview                                         # live preview at :3000 (unverified, no page script)
```

Worked examples to copy from: `docs/implication-composition/` (the reference example:
numbered results, Mermaid, a widget, a Mathlib corollary, a tag), and the real entries
`docs/spanning-tree-min-split/` (several Lean modules, a definition export, AI-use and
acknowledgement notes) and `docs/lagrangian-duality-gap/` (a long single-module proof).

