# TODO

Planned and proposed work on the Lemmata Repository, roughly in order. Not rendered on the
site. The repository is public; issues and pull requests are welcome too.

## Next

- **Disambiguation for git-derived authors.** Entries without `contributors` take names from
  git and have no ORCID iD. Ask contributors to add `contributors` with their iDs (and add
  ours to the existing entries).

## Security follow-ups (review of 2026-10-22)

- **Render in a container that sees only the source.** The validator now refuses every
  file-reading directive outside an entry's own files, in all fence styles (tested). As a
  second layer, MyST should run in a container with only the source copy and the theme,
  so a future bypass finds nothing to read. Today render has no token and no secrets, so
  little could leak, but that should not depend on nobody adding one.
- **Widgets run contributor JavaScript on our origin.** Decide: accept with review (now),
  or sandbox widgets in an iframe on a separate origin.
- **Split tools/lemmata.mjs** into testable modules, after the tests exist.

## Later

- **Build time grows with the number of entries.** Compiling is cached since 2026-10-22
  (only changed entries recompile), but every build kernel-replays all modules: ~5½ min to
  live for 6 entries. Skipping the replay for unchanged modules is only sound if the key
  covers the module's bytes, its imports' approvals, and the Mathlib and checker versions.
  Revisit if the replay starts to dominate.

- **Every notation links to its definition.** Automatic links from notation in the prose to
  the `prf:definition` (and Lean declaration) that introduces it. Needs a notion of which
  symbol a definition introduces; a modest first step is linking every bound definition to
  its Lean code, as for theorems.
- **Reference titles as links.** MyST renders a reference as fixed text with the DOI as the
  only link and has no option to link the title instead. Possible in the page script, but it
  would have to guess where the title ends, which breaks on titles containing a full stop.
- **Per-reader settings,** e.g. "start with all proofs folded", kept in the browser.
- **"Edit this page" link** to GitHub's web editor, for small prose fixes by pull request.

## Future version: community features

These need accounts, stored state and moderation, which the static site does not have.

- **Wiki-style editing** with edit summaries and common tags, and a choice between the
  original author's version and the community version.
- **Discussion page per entry** (reddit/HN-style threads). Giscus comments, live since
  2026-10-21, are a first version.
- **Inline annotations** on selected text and math, private, shared with a group or public,
  with tags such as "typo" and TeX support, as hypothes.is does. hypothes.is itself can be
  embedded with one script as an experiment.
