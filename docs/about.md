---
numbering:
  headings: false
title: About
---

The Lemmata Repository is an experimental mathematics repository: each entry is a result
written for people and formalized in Lean 4 on Mathlib, and every formal statement is
checked by Lean's kernel before it is published. See [what "checked" means](checked.md)
and the [changelog](changelog.md) for how the site has developed.

Lemmata is a home for **formalized results that are worth sharing before, or without, a
full paper**: lemmas and constructions that may never become a paper of their own but are
still useful to others, and results at a stage before a preprint — a way to disseminate
them early, with the Lean proof as evidence. It is equally a place to **archive the
formalization of results from a paper**, preprint or published, linked to it, so the
proofs have a permanent, citable home next to the text. Entries are self-contained, and
each has a stable identifier to cite.

Entries are web pages rather than papers. They are written in MyST Markdown and rendered
as HTML with KaTeX, so an entry can use what fits the mathematics — numbered results,
diagrams, interactive widgets — instead of a fixed paper layout. We chose HTML on purpose:
almost any information can be represented in it well, more richly than in a static
document [@shihipar2026using].

The repository is also built to be read by machines, and by language models in
particular. [`/llms.txt`](https://lemmata.iol.berlin/llms.txt) is a plain-text overview of
every entry with its identifier and status;
[`/lemmata.json`](https://lemmata.iol.berlin/lemmata.json) is a machine-readable index with
every exported Lean declaration, its verification status and axioms, and a BibTeX entry.
Every entry links the Lean source of each result, and its page can be downloaded as
Markdown. Coding agents that want to contribute follow AGENTS.md (linked below), the
contribution procedure written for them.

The repository is born out of the Agentic AI for Mathematics (EF-LiOpt-3) project at the Berlin Mathematics Research Center MATH$^+$ (EXC-2046/2, project ID 390685689), funded by the Deutsche Forschungsgemeinschaft (DFG, German Research Foundation) under Germany's Excellence Strategy. In its initial phases it is maintained by the [IOL lab](https://iol.zib.de) at the Zuse Institute
Berlin (ZIB) and TU Berlin with the aim to transition to a community driven model in the very near future. 

## Contributing

Anyone can contribute. An entry is published once its pull request has been reviewed and
merged, and the site has built it and checked every formal statement.

```{include} _generated/contributing-body.md
```

By default an entry, prose and Lean alike, is published under the
[Creative Commons Attribution 4.0 International license (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/).
A contribution may specify another license, as long as it is compatible with the aim of the
repository: entries must remain freely readable, reusable and buildable upon. Currently
accepted besides the default are [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/),
[CC0 1.0](https://creativecommons.org/publicdomain/zero/1.0/) and
[Apache 2.0](https://www.apache.org/licenses/LICENSE-2.0). Each entry shows its license
under its title. Adaptations must retain the applicable upstream license and attribution
notices. Please contribute only material you have the right to license in this way.

## Removal of contributions

Like arXiv, the repository is a permanent record. Once an entry has been published and
received its identifier, it is not removed: others may cite it, and other entries may build
on its Lean code, which would stop compiling if it disappeared. An entry can instead be
marked as **withdrawn**. It then stays available under its identifier, together with a
notice of the withdrawal and the reason given, and is no longer listed as a current entry.
Errors should be corrected by updating the entry; every published version remains
traceable through the entry's history.

Material can only be removed outright in exceptional cases, such as legal reasons or
copyright violations. Requests for removal or withdrawal go to the maintainers.

## Support

We gratefully acknowledge the support of:

:::{div}
:class: lemmata-supporters

[![MATH+, the Berlin Mathematics Research Center](_static/logos/mathplus.png)](https://mathplus.de/)
[![Zuse Institute Berlin](_static/logos/zib.svg)](https://www.zib.de/)
[![RISE, powered by Zuse Institute Berlin](_static/logos/rise.png)](https://www.zib.de/)
:::
