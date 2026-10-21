# TODO

Planned and proposed work on the Lemmata Repository, roughly in order. Not rendered on the
site. Add items here rather than to issues while the repository is private.

## Next

- **Statement, Lean and verification together.** Below each bound result, show its Lean
  statement, its verification badge and a link to the exact lines of the proof file; the
  panel at the end becomes a summary. The same for definitions. Being planned (2026-10-21).
- **Comments with Giscus.** The code path exists (`GISCUS` in `tools/lemmata.mjs`, off). It
  needs a *public* GitHub repository with Discussions enabled (the content repository once
  public, or a separate `lemmata-discussions`), the Giscus app installed on it, and its
  repo/category ids filled in.

## Later

- **Every notation links to its definition.** Automatic links from notation in the prose to
  the `prf:definition` (and Lean declaration) that introduces it. Needs a notion of which
  symbol a definition introduces; a modest first step is linking every bound definition to
  its Lean code, as for theorems.
- **Reference titles as links.** MyST renders a reference as fixed text with the DOI as the
  only link and has no option to link the title instead. Possible in the page script, but it
  would have to guess where the title ends, which breaks on titles containing a full stop.
- **Per-reader settings,** e.g. "start with all proofs folded", kept in the browser.
- **Author identities.** Author pages are keyed by the displayed name, so two people with one
  name share a page. ORCID iDs in `contributors` would make them unique.
- **"Edit this page" link** to GitHub's web editor, for small prose fixes by pull request.

## Future version: community features

These need accounts, stored state and moderation, which the static site does not have.

- **Wiki-style editing** with edit summaries and common tags, and a choice between the
  original author's version and the community version.
- **Discussion page per entry** (reddit/HN-style threads). Giscus covers a first version.
- **Inline annotations** on selected text and math, private, shared with a group or public,
  with tags such as "typo" and TeX support, as hypothes.is does. hypothes.is itself can be
  embedded with one script as an experiment.
