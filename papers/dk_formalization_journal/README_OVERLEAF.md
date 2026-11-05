# Editing the manuscript in Overleaf

Upload `dk_formalization_overleaf.zip` as a new project. Set the compiler to
**LuaLaTeX** and the main document to **paper.tex**. The supplied figures compile
without Python, Manim, Lean, or access to the proof repository.
The upload uses `latexmkrc` and leaves output paths under Overleaf's control;
the repository's local `.latexmkrc` is not included.

At the top of `paper.tex`, set `\DKAuthorStyletrue` for colored mathematical
symbols, hover reminders, and author–year citations. Set `\DKAuthorStylefalse`
for the journal's numbered citations and monochrome symbols. Both use the
supplied Springer Nature class. Anonymous review remains a separate switch.

The repository is the primary source. The Overleaf project uses the same
filenames and `figures/` paths as `papers/dk_formalization_journal/`; there is
no separate copy of the manuscript to maintain in the repository.

To bring collaborator edits back, download the Overleaf **source ZIP**, extract
it elsewhere, and copy the changed `.tex` and `.bib` files into the manuscript
directory under the same names. Review `git diff` before committing, especially
if the same file was edited locally. Copy any newly authored source files too.
Generated PDFs and figures do not replace their repository generators.

To send local edits to Overleaf, run `make overleaf` in the manuscript directory
and upload the files from the resulting ZIP over the existing project. Download
outstanding collaborator changes first. Overleaf is a review/editing copy;
these steps do not set up automatic two-way synchronization.

`make submission` produces a separate publisher archive with a generated,
single-file `paper.tex`, its compiled PDF, bibliography/styles, editable PGF
figures, and PDF/EPS figure exports. The publisher copy uses journal style.
Do not overlay that flattened `paper.tex` back onto the repository or Overleaf;
use the modular Overleaf archive for collaborative edits.

Figures were drawn with Matplotlib's PGF backend and typeset with LuaLaTeX.
Their PDF/EPS exports are vector artwork; the numerical models and generators
are maintained in the repository. No AI image generator was used for them.
