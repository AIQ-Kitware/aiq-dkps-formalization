# Research in the Mathematical Sciences preparation

The current manuscript is *Formalizing Davis--Kahan Perturbation Theory in
Lean 4*. The repository manuscript is authoritative; Overleaf is a collaborative
editing copy with the same filenames. The publisher export is generated.

From `papers/dk_formalization_journal/`:

```bash
make paper          # current style; journal mode is the default
make author-paper   # colors, hover reminders, author--year citations
make overleaf       # build/dk_formalization_overleaf.zip
make submission     # build/dk_formalization_submission.zip
```

The top-level `\DKAuthorStyletrue` / `\DKAuthorStylefalse` boolean controls
citation style, symbol colors, and hover reminders. The publisher export sets
journal mode regardless of the local editing choice.

Upload the modular ZIP to Overleaf and select LuaLaTeX and `paper.tex`.
[README_OVERLEAF.md](../README_OVERLEAF.md) explains how to overlay collaborator
edits and local edits without maintaining two drafts. The publisher ZIP contains
a single expanded manuscript TeX file, separate vector figures, bibliography
and class/styles, and a PDF compiled from those exported sources. Do not copy
its flattened manuscript back into the working tree.

[GUIDELINE_AUDIT.md](GUIDELINE_AUDIT.md) records the manuscript requirements,
changes, and author-supplied declarations against the supplied
[guidelines](../submission_guidelines.md) and the official journal page.
The supplied template class and bibliography styles are tracked, unchanged;
all ZIPs, PDFs, EPS/PGF exports, and build intermediates are regenerable and
ignored. The mathematical result inventories and Lean declarations are unchanged.

Before actual submission, the corresponding author handles coauthor agreement,
institutional release, and any copyright permissions applicable to external
material. No journal or Overleaf upload is performed by the packaging commands.
The older letters and literature notes here are preparation records, not
additional files automatically attached to either archive.
