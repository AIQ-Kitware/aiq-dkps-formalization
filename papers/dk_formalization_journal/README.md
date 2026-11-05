# Formalizing Davis--Kahan Perturbation Theory in Lean 4

**Current journal manuscript:** `paper.tex`. This is a formalization paper
covering the 1970 Davis--Kahan source, its Lean operator-theory prerequisites,
a source correction to Proposition 4.4, and one follow-on matching example.

For scientific scope and publication boundaries, read
[FORMALIZATION_PAPER_SCOPE.md](FORMALIZATION_PAPER_SCOPE.md).

For editing, start with [AGENTS.md](AGENTS.md), the
[shared positive style guide](../STYLE_GUIDE.md), and the
[journal style guide](STYLE_GUIDE.md). [AUTHORING_NOTES.md](AUTHORING_NOTES.md)
records the current author-review decisions, pending manuscript changes, and
paths to result mappings, provenance evidence, and the optional upstream campaign
checkout. The older dated plans in `PAPER_CONTEXT.md` are historical checkpoints.

The older mathematics-first manuscript, including the complete two-parameter
spectral-penalty theory, optimizer classifications, real matching, nuclear
endpoint, and infinite-dimensional extensions, is preserved as a buildable
source snapshot in [`../optimal_spectral_transport/`](../optimal_spectral_transport/).
Existing transport-oriented `.tex` files in this directory are historical
working sources and are **not included by `paper.tex`**. Work on that broader
mathematics belongs in the companion paper directory.

The retained 29 source targets consist of 28 formalized statements and one
formally refuted proposition. For traceable support see the source inventory,
`claims_to_evidence.md`, and the formalization appendices. Historical priority
of new transport results remains a separate literature question.

## Build

The manuscript uses the supplied Springer Nature `sn-jnl` class and mathematics
bibliography styles. Journal mode is the default. At the top of `paper.tex`,
flip `\DKAuthorStylefalse` to `\DKAuthorStyletrue` for colored symbols,
hover reminders, and author–year citations. The journal class and mathematical
content stay the same.

```bash
make -C papers/dk_formalization_journal paper
```

The PDF is written to `build/paper.pdf`. The build requires `latexmk`,
LuaLaTeX and BibTeX. Noto Color Emoji is optional for review-note icons;
the notes use text labels when that font is unavailable.
The project selects LuaLaTeX even for `latexmk -pdf`, including LaTeXBox builds.
Configure editor builds to use `latexmk`
from this directory so they read `.latexmkrc`. If an older build mixed
auxiliary files in the source directory and `build/`, clean both once:

```bash
cd papers/dk_formalization_journal
latexmk -outdir=. -C paper.tex
latexmk -gg -pdf paper.tex
```

The project keeps the previous PDF when compilation fails. To diagnose a
build that says “Nothing to do” but exits with “gave an error in previous
invocation”, inspect `build/paper.log` for the original LaTeX error. Latexmk
remembers a failed run even when no inputs have changed. Correct the source
and run `make` again. To retry unchanged sources after resolving an external
problem, use `latexmk -g -pdf paper.tex`; this reruns the compiler and still
reports errors normally.

`make author-paper` builds `build/paper-author.pdf` with the author's style
without changing the boolean or the main PDF.

## Overleaf and journal packages

From this directory:

```bash
make overleaf
make submission
```

The outputs are `build/dk_formalization_overleaf.zip` and
`build/dk_formalization_submission.zip`. Upload the first ZIP to Overleaf,
select **LuaLaTeX**, and use **paper.tex** as the main document.

The Overleaf ZIP preserves this directory's manuscript filenames and `figures/`
paths. It contains the needed sources, class/styles, generated vector figures,
and compiled PDF, without the proof repository or figure-generation dependencies.
Download collaborator edits as an Overleaf source ZIP and overlay the edited
`.tex`/`.bib` files here, reviewing `git diff` before committing. To send local
edits back, rebuild and upload the modular Overleaf ZIP. This repository remains
the primary source; no automatic synchronization or second maintained draft is
introduced. See [README_OVERLEAF.md](README_OVERLEAF.md) for the editing workflow.

The publisher ZIP is generated from those same sources in journal style. Its
`paper.tex` expands the included manuscript files into one document and uses
separate PDF figures; editable PGF and EPS exports are supplied too. It is
compiled independently before packaging. Do not overlay this flattened export
back into the source tree.

The requirements audit is in
[submission/GUIDELINE_AUDIT.md](submission/GUIDELINE_AUDIT.md), alongside the
unaltered [submission guidelines](submission_guidelines.md).

To diagnose a silent LaTeXBox background build, run these commands in Vim with `paper.tex`
open (these settings affect only the current session):

```vim
:lcd %:p:h
:let g:LatexBox_latexmk_async = 0
:Latexmk!
:LatexErrors
```

## Matching proof study note

`matching_proof_study.tex` expands Theorem 5 using the same six steps and
lettered inferences as the article. Each inference is followed by its
justification, with the first-variation derivation, block calculations,
and prompts for explaining the proof aloud. It is built separately from the
article.

From this directory, run `make matching-study` to produce
`build/matching_proof_study.pdf`. The mathematical symbol definitions and hover
reminders use the article's shared registry. The TeX source is tracked; the
regenerable PDF is ignored.

## Manuscript figures

Figure generators and their numerical models are tracked. Generated PGF,
PDF/SVG exports, and previews are gitignored. Both `make paper` and direct
`latexmk -pdf paper.tex` regenerate missing or stale figures before compiling;
the latter also supports Vim/LaTeXBox. The manuscript inputs live PGF so its
LaTeX fonts, symbol colors, and hover reminders apply inside figures.
Slides are rendered separately with Manim.
To regenerate the counterexample from the existing checked numerical model in `visualizations/dkvis/prop44.py`, run:

```bash
make -C papers/dk_formalization_journal counterexample-figure
```

The sine-theta geometry and weighted-matching figures use the numerical models
shared with the Manim slides. The first adapts the residual triangle from
`S05Residual` and the exact component split from `S08Why`; the second shares
its three-angle example with `N08MatchingGraph`. Regenerate their
PGF sources and standalone vector exports with:

```bash
make -C papers/dk_formalization_journal teaching-figures
```

Use the `figures` target to regenerate all three manuscript figures. Regeneration
requires GNU Make, LuaLaTeX, and Poppler's `pdftocairo`/`pdftoppm`
in addition to Matplotlib and NumPy. These dependencies are also needed on the
first paper build. The two authored SVG sources retained under `figures/`
are independent of the generated figures.

Derived analysis tables under `snapshots/` are also gitignored. Their generators
are retained; `make accounting` refreshes the optional repository-analysis views,
and `make literature` prepares its dependency tables before compiling. Dated
external observation JSON remains tracked as input data. The main paper build
does not run accounting analyses or contact external services.

## Draft controls

The main switch is `\DKAuthorStyletrue` / `\DKAuthorStylefalse` before
`\documentclass`. It selects the matching Springer bibliography style,
mathematical colors, and hover reminders together. The preamble also provides
independent controls:

- Set `\DKAnonymoustrue` in place of `\DKAnonymousfalse` to omit author and
  affiliation details, identifying artifact links, and acknowledgments.
- Set `\DKSymbolTooltipsfalse` after the symbol-macro input to disable the
  default glossary reminders on hover. Definitions, coordinate spaces, and
  local roles live in the optional reminder argument of each semantic symbol
  declaration in `math_symbol_colors.tex`. The final argument supplies a short
  description for the notation appendix and the fallback hover text. Native PDF
  tooltips have no navigation action and require viewer support. They cover `\sym` and `\like`
  expressions in text, equations, captions, and the three live PGF figures.
  In Okular, enable **View → Show Forms** to expose the hover regions. Other viewers may enable PDF tooltips automatically.
- Set `\DKColoredSymbolsfalse` before the symbol-macro input to override
  mathematical colors. The palette is shared with the Manim visualizations.

For wrapper builds, defining `\DKNoSymbolTooltips` before `\input{paper.tex}`
disables the hover annotations. Defining `\DKAnonymousReview` enables
anonymous mode; `\DKMonochromeMath` enables monochrome symbols. Set these
wrapper flags before `\input{paper.tex}`.
`\DKUseAuthorStyle` selects author style in a wrapper;
`\DKJournalStyle` forces journal style. Journal mode uses square-bracket
numbered citations and disables the hover widgets. The two supplied `.bst`
files are selected by the class; no manual bibliography-style edit is needed.

The `\jonsays`, `\agentsays`, and `\jonrsp` macros remain defined for the
next review round; their calls have been removed from the revised manuscript.

## Lean artifact and reproduction

The root `lean-toolchain` and `lake-manifest.json` pin the Lean compiler and
library dependencies. From the repository root, run:

```bash
lake exe cache get
lake build
```

A focused check of the direct-rotation aggregate and the source-facing
Proposition 4.4 counterexample is:

```bash
lake exe cache get
lake build \
  DavisKahan.FiniteDimensional.DirectRotation.All \
  DavisKahan.Sources.DavisKahan1970.Section4SmallAngle
```

The paper PDF is generated with:

```bash
make -C papers/dk_formalization_journal paper
```

The paper-facing source wrappers reside in
`DavisKahan/Sources/DavisKahan1970`; local reusable foundations are in
`ForTauCeti`, with some modules replaced by accepted upstream `TauCeti`
implementations. The source inventory is
`dev/davis-kahan-1970-formalization-result-inventory.json`.

The explicit trace-norm counterexample is in
`DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean`,
with the arbitrary-angle family in
`DavisKahan/FiniteDimensional/DirectRotation/SmallAngleCounterexample.lean`
and its source wrapper in
`DavisKahan/Sources/DavisKahan1970/Section4SmallAngle.lean`.

The nuclear matching reduction is in
`DavisKahan/FiniteDimensional/DirectRotation/RealNuclearMatching.lean`.
The full transport optimization manuscript is maintained separately in
`papers/optimal_spectral_transport`.

## Historical reading map

The manuscript's historical section brings together several distinct
lines of prior scholarship. Useful extended accounts include:

- C. C. Paige and M. Wei (1994), *History and Generality of the CS
  Decomposition*, for Jordan's principal-angle geometry, Davis--Kahan,
  Stewart's matrix decompositions, and direct rotation.
  DOI: `10.1016/0024-3795(94)90446-4`.
- Barry Simon (2018), *Tosio Kato's work on non-relativistic quantum
  mechanics: part 1*, Section 5, for Sz.-Nagy's nearby projections,
  Kato's intertwiner, and the history of pairs of projections.
  DOI: `10.1007/s13373-018-0118-0`.
- A. Bottcher and I. M. Spitkovsky (2010), *A gentle guide to the
  basics of two projections theory*, for the Halmos model and the
  structure of the algebra generated by two projections.
  DOI: `10.1016/j.laa.2009.11.002`.

These complement the original Davis (1958), Davis--Kahan (1970),
Kato (1966), and Rosenblum papers. The historical section explains
how their mathematical ideas become prerequisites of the formalization.


## Historical exposition

The manuscript's historical chapter traces the questions and results
needed for Davis--Kahan: principal-angle geometry, variational
eigenvalue approximation, spectral projection transport, the
Sylvester/residual argument, and unitarily invariant operator ideals.
Its annotated dependency table identifies which formal foundations
realize each historical mathematical component. Primary papers and
historical surveys are cited in `references.bib`.

The three manuscript illustrations are included as `figures/Fig1.pgf`,
`figures/Fig2.pgf`, and `figures/Fig3.pgf`. Generated files stay ignored in Git
and are included in export ZIPs so collaborators can compile them directly.
