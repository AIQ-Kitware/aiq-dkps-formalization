# Journal preparation

**Manuscript:** *Formalizing the Davis--Kahan Perturbation Theorems in Lean*.

The source-faithful 29-result inventory is unchanged: 28 results proved at
reviewed source scope, and Proposition 4.4 refuted as printed. The verified
small-angle family works in real dimension four at every positive acute angle;
the original complex phase mechanism is credited to Davis and Kahan.

The October 23 development also proves a sharp uniform
`sec(alpha/2)` comparison for arbitrary unitarily invariant seminorms, plus
a global real-family trace-minimum theorem. The complex exact trace-norm
optimum has been formalized for supplied principal-plane models, not for
every arbitrary complex pair. The latter all-pairs statement is available
only as a clearly marked optional red-box working draft, disabled by default.
See `VALIDATION.md` and `LITERATURE_AUDIT.md`.

These are alternative journal inquiries, not simultaneous formal submissions;
no inquiry is represented as sent. Research in the Mathematical Sciences is
the initial target, and Annals of Formalized Mathematics is an alternative.

## Before submitting

1. Rebuild the pinned Lean project and targeted quantitative modules using
   `VALIDATION.md` commands. Retain the source-to-Lean correspondence review
   separately from the build result.
2. Obtain human/coauthor sign-off on the mathematical arguments, priority
   framing, title, author order, institutional affiliations, and AI disclosure.
3. Confirm competing-interest, funding, contact and release declarations
   required by the selected venue. Keep the existing DARPA acknowledgment.
4. Freeze the repository revision and dependencies for a persistent artifact.
5. Review publication dates and printed-page citations against
   `PROPOSITION_4_4_LITERATURE_MAP.md` before final submission.
6. Submit to only one journal at a time. Nothing has been sent automatically.

## Venue checks (official pages checked 20 October 2026)

Research in the Mathematical Sciences requires an abstract of 150--250 words,
4--6 keywords, MSC codes, editable LaTeX sources and PDF, and relevant
Statements and Declarations. The revised draft includes an abstract, six keywords, and proposed MSC2020
codes 47A55, 15A42, 68V20; recheck the word count against the final source. Its neutral article class is suitable for an inquiry;
the publisher recommends its own template for submission. Confirm any
editor-requested formatting after the scope reply.

- https://link.springer.com/journal/40687/submission-guidelines
- https://link.springer.com/journal/40687/contact-the-journal

AFM accepts a preferred LaTeX class initially, requires an open archived paper
and accessible formal artifacts for formal submission, and asks for explicit
links between principal mathematical results and code. Its author instructions
say only human-authored manuscripts are accepted and require disclosure of
AI involvement in code and prose. Because this revision includes generative
AI drafting, the AFM inquiry explicitly asks about that policy rather than
assuming eligibility. Substantive human review remains necessary for either
journal.

- https://afm.episciences.org/page/aims-and-scope
- https://afm.episciences.org/page/instructions-for-authors

## Files to submit eventually

The manuscript uses paper.tex, counterexample.tex, sharp_displacement.tex,
appendix_process.tex, appendix_notation.tex, and references.bib. Keep the exact
Lean artifact and validation evidence separately accessible. A buildable manuscript-source
bundle is supplied alongside the overlay; it contains no proof-library copy.
The supplement files in this directory are preparation records, not automatic
journal attachments.
