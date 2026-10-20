# Validation record: 20 October 2026

Base repository commit: `56274cb8cf10a632b62f394fa51391bc6e1b44e3`.
Source archive: `aiq-dkps-formalization-source-2026-10-20T160615-5-56274cb8cf10.tar.gz`.

## Established original results

The supplied development has 29 source-level targets: 28 source-scope proofs
and the checked fixed-angle Proposition 4.4 refutation. Those verification
claims are preserved. The source inventory, `lean-toolchain`,
`lake-manifest.json`, and `lakefile.toml` are byte-for-byte unchanged from the
base commit. Four existing coordinate/basis helper lemmas were made public
without changing their statements or proofs, to avoid duplicating them.

## Additional parameterized theorem

**Lean compiler validation: not performed in the overlay-author environment.**
No Lean/Lake installation or cached dependency build was available, and network
access could not retrieve them. This limitation concerns the new extension,
not the original verified development. The new proof source is a candidate
implementation and may require elaboration/tactic repairs in the pinned build.

The conventional proof is in `counterexample.tex`. The new source identifies
acuteness and the exact principal angles, identifies the canonical rotation
via its intertwiner's modulus, computes the displacement singular values,
and derives the strict comparison and arbitrary-threshold existential theorem.
Its main-file SHA-256 is `b761037a3fe471a28d60a8aa7d34b3f28c7a1a31dcbcc058e5b37a94f33733fc`.

Static inspection found no proof admissions, new axioms, or opaque declarations
in the three new Lean files. Their direct local imports resolve to source
files. This inspection is not a kernel proof check. The separate axiom audit
has been written but its commands have not been executed by Lean here.

## Algebra and manuscript checks actually run

- SymPy 1.14.0: all 13 exact identities in
  `scripts/small_angle_symbolic.py` passed, including both orthogonality checks,
  target projection and frame, canonical intertwiner, both Gram spectra,
  recovery of the existing pi/4 matrix, and the trigonometric trace ratio.
  The strict inequality follows in the mathematical proof from
  `sin(theta/2) > 0` and `cos(theta/2) < 1` on the stated interval.
- LaTeX/BibTeX: the revised manuscript builds to 18 pages. This environment
  used `bibtex8` behind a local `bibtex` command shim. Final logs contain no
  overfull boxes, undefined references, or undefined citations.
- Abstract: approximately 219 words, treating each displayed inline
  mathematical expression as one token; six keywords and MSC codes present.
- Every page was rendered and visually inspected; the extended counterexample
  section, gap hypotheses, signature, tables, and artifact instructions were
  reviewed for page overflow and legibility.
- `git diff --check` passed. The resource-accounting publish command reported
  that there was nothing to publish; no usage data was invented.

## Local compiler gate

From the repository root, use the pinned environment and retrieve the cache
before building:

```bash
lake exe cache get
lake build \
  DavisKahan.FiniteDimensional.DirectRotation.SmallAngleCounterexample \
  DavisKahan.Sources.DavisKahan1970.Section4SmallAngle \
  DavisKahan.Sources.DavisKahan1970.Audits.SmallAngleCounterexample
```

The audit prints dependencies for the principal-angle identification, trace
formulas, strict comparison, and arbitrary-threshold result. Inspect them for
admissions or project-specific unproved axioms. A successful build must precede
any claim that the new family is formally verified. Retain its actual output
and compiler/dependency revisions. Re-run the normal project build only after
this focused gate; use `lake exe cache get` first there as well.

The extension is intentionally a separate source-facing import and is not added
to the existing `DavisKahan.All` or source inventory. After validation, an
explicit import can be added to the ordinary build in a follow-up change.

## Reproduce the mathematical calculation and PDF

```bash
python papers/dk_formalization_journal/scripts/small_angle_symbolic.py
make -C papers/dk_formalization_journal paper
```

The algebra script is optional and needs SymPy. It is not a Lean substitute.
On installations with only `bibtex8`, the equivalent manuscript command is:

```bash
cd papers/dk_formalization_journal
latexmk -e '$bibtex = "bibtex8 %O %B";' -pdf paper.tex
```

After a successful Lean check, replace only the new-extension status paragraph
in Appendix F.1 and this record with the observed build evidence; the inquiry
letters may then explicitly call the new family formally verified. Do not
change historical source-target counts. Author approval, conflicts declarations,
AFM policy clarification, and final submission remain separate actions.
