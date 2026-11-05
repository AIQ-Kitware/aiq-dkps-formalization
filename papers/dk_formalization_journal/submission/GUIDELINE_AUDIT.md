# Research in the Mathematical Sciences: manuscript audit

Checked 4 November 2026 against the author's
[guidelines](../submission_guidelines.md), the
[official journal instructions](https://link.springer.com/journal/40687/submission-guidelines),
and the supplied Overleaf template, version 3.1 (December 2024).
This file is an author record and is not included in the rendered manuscript.

| Requirement | Manuscript or export |
| --- | --- |
| Publisher template | `paper.tex` uses the supplied `sn-jnl.cls`, with the mathematics numbered bibliography style by default. |
| Title and human authors | Existing title, author order, and four human authors retained; the class marks Jonathan Crall as corresponding author and prints the existing institutional emails. |
| Full affiliations | Author supplied Clifton Park, NY, USA for Kitware and the Department of Applied Mathematics and Statistics for Johns Hopkins. The latter is listed in Baltimore, MD, USA. |
| Abstract, 150–250 words | Approximately 161 words, with no citations or unexplained acronym; Q-norm is described in the abstract. |
| Four to six keywords and MSC | Six keywords; MSC2020 codes 68V20, 47A55, 15A42. |
| Numbered square-bracket citations | Journal mode selects `sn-mathphys-num`; the author-style boolean selects `sn-mathphys-ay` and colored symbols. The class loads Natbib. |
| Published references and online documents | Updated the DKPS reference to its published ICML 2026/PMLR version. Dedecker–Loreaux's preprint is attributed and linked in the text rather than listed as a published paper. Public software sources retain their online-document references. Only cited entries appear in the bibliography. |
| Full DOI links | The supplied bibliography style renders the DOI fields as `https://doi.org/...`. Added the missing DOI fields for Davis (1965) and Davis–Kahan (1969), verified against Crossref's registered metadata. No DOI is invented for an older source or assigned from a different edition. |
| Decimal headings, at most three levels | Sections, subsections, and subsubsections retained. The contributions label is ordinary bold text rather than a fourth-level heading. |
| Acknowledgments and funding | Full DARPA acknowledgment is in the title matter, with the funder's name corrected to Defense Advanced Research Projects Agency. Funding and contract number also appear under Statements and Declarations. |
| Competing interests | The author reported none to their knowledge; the manuscript states that the authors declare no competing interests. |
| Data/code availability | Statements and Declarations links the public proofs, result mapping, provenance, figure generators, and manuscript sources. No empirical dataset or archived release is invented. |
| AI assistance | Existing substantive disclosure is retained under Statements and Declarations, describing assistance with formalization, writing, and the matching result. AI systems are not listed as scholarly authors. |
| Applicable declarations | No human-participant or animal study is reported. No unnecessary consent or clinical-trial boilerplate is inserted. ORCIDs and an individual author-contribution statement are optional and have not been invented. |
| Figure names and editable sources | The three illustrations are `figures/Fig1` through `Fig3`. Both exports supply editable PGF and vector PDF; the publisher export also supplies EPS. Matplotlib/PGF and LuaLaTeX are identified in the export README and PDF metadata. |
| Figure size, lettering, and readability | Figures are placed at 119 mm. An 8.2-inch source canvas with 14–21 pt labels gives approximately 8–12 pt lettering at that width. Explanations remain in captions; panels use lowercase labels. Guide lines are darkened and solid/dashed lines or labels distinguish the roles. Mathematical lettering remains in the manuscript's LaTeX fonts. |
| Figure captions | The class supplies bold “Fig.” and the Arabic number without punctuation after it. Removed terminal caption punctuation. Captions identify the components and the source comparison. |
| Tables and appendices | Both summary tables remain in Appendix C, with captions and the original result IDs. No mathematical target or theorem statement is removed to fit the template. |
| Editable sources and compiled PDF | `make overleaf` supplies the modular manuscript; `make submission` expands its TeX inputs into one manuscript, uses separate PDF figures, and compiles those exported sources. Both archives include a compiled PDF and the class/bibliography styles. |
| Collaborative editing | The modular archive preserves repository filenames and directory structure. Source ZIPs can be overlaid after reviewing simultaneous edits. The repository remains authoritative. |

The upload's `latexmkrc` leaves job names and output directories to Overleaf,
as advised in its [compilation documentation](https://www.overleaf.com/learn/how-to/How_does_Overleaf_compile_my_project%3F).
The local `.latexmkrc` and its `build/` output directory are not exported.

Validation: both local styles compile, and the modular upload was extracted
outside the repository and compiled with automatic user configuration disabled
(`latexmk -norc -r latexmkrc -pdf paper.tex`). The single-TeX publisher export
also compiles independently. These builds have no unresolved citations or
references, missing characters, or overfull lines. Figure PDF fonts are embedded;
the title page and figure layouts were inspected after resizing.

The publisher's general typography advice is applied without changing the
paper's established Hilbert-space notation: variables remain italic and named
operators/functions upright. Figure roles can be recovered without symbol
colors. There are no externally generated bitmap illustrations or generative-AI
images in the submitted figures.

The submitted-work declarations, coauthor agreement, institutional release, and
any permissions the journal requests remain the corresponding author's actions
at actual submission. Packaging does not submit the paper or attest that those
actions have occurred.

## Template provenance

The following files are copied byte-for-byte from
`DK_Formalization___Res__Math_Sci_.zip`; their copyright and license notices
are retained:

- `sn-jnl.cls`
- `bst/sn-mathphys-num.bst`, placed at `sn-mathphys-num.bst`
- `bst/sn-mathphys-ay.bst`, placed at `sn-mathphys-ay.bst`

The input ZIP's SHA-256 is
`9f582cfd3562114d80bf5d8fd593119d1339c0b0b5e5b3b379fb03e9eb4f7287`.
The other sample articles, placeholder figures, and template manuals are not
copied into the manuscript or its upload bundles.

## Bibliographic evidence

- [Helm, Johnson, and Priebe: ICML 2026 proceedings](https://proceedings.mlr.press/v306/helm26a.html).
- [Dedecker and Loreaux: current arXiv record](https://arxiv.org/abs/2501.15639), which gives no journal publication reference.
- [Davis (1965): registered DOI metadata](https://api.crossref.org/works/10.1016%2F0022-247X%2865%2990066-1).
- [Davis–Kahan (1969): registered DOI metadata](https://api.crossref.org/works/10.1090%2FS0002-9904-1969-12330-X).
