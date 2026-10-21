---
numbering:
  headings: false
title: Changelog
---

What changed in the archive that a reader should know about: new entries, corrections to
published entries, and changes to what "checked" means. Routine edits are not listed; every
entry shows its own last change and links to the exact commit.

Newest first. Add an item in the same pull request as the change it describes.

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
