# Journal preparation

**Working title:** Davis--Kahan (1970) in Lean: Formalization, Counterexample,
and Repair.

This directory contains coauthor-facing preparation material. The two inquiries
are alternative scope inquiries, not simultaneous formal submissions. Neither
has been sent. Research in the Mathematical Sciences is the intended first
choice; AFM is the alternative. The scientific manuscript is shared.

## Mathematical claim

The original 29-target inventory is unchanged: 28 source-scope proofs and the
fixed-angle refutation of Proposition 4.4 retain their established verification
status. The additional family gives failure for every theta in (0, pi/2),
therefore below every positive proposed angle threshold. The new Lean source
has **not been compiled in the overlay author's environment**. See VALIDATION.md.
Do not turn this local limitation into a qualification of the original results.

The contribution is the explicit small-angle refutation and failed-proof-step
diagnosis alongside the broad formalization. General trace-norm failure and
Q-norm minimization precede this work. No global minimizing property is claimed
for the competing rotation, and no priority claim is made for the known norm
phenomenon. See LITERATURE_AUDIT.md.

## Before sending an inquiry

Review the mathematical description with the coauthors. The current drafts
attribute machine-checking to the verified original artifact and present the
parameterized family with its conventional proof. Once the new Lean module
and axiom audit pass, the letters may also describe the family as formally
verified. Update the corresponding appendix paragraph on actual build evidence;
do not infer a Lean build from successful PDF compilation.

For RIMS, request editorial routing using the official contact page. For AFM,
use its published editorial address. A scope inquiry does not promise a
review or acceptance. Do not send these files, internal validation notes,
or the entire history as an unsolicited bundle; the short body and an
agreed draft PDF suffice when requested.

## Before formal submission

1. Run the Lean commands in VALIDATION.md and inspect the printed dependencies.
   Update only evidence-backed status statements. Independently check the
   conventional parameterized proof and its identification of the canonical
   rotation against the Lean interface.
2. Obtain coauthor approval of the final mathematics, title, author order,
   affiliations, AI disclosure, acknowledgments, and any institutional release
   requirements. This overlay does not certify that approval.
3. Supply a confirmed competing-interests statement under RIMS's requested
   Statements and Declarations heading. None was invented here. Confirm city,
   country, and ORCID information for all authors, and all funding/tool subsidies.
   The existing DARPA acknowledgment is preserved.
4. Freeze the actual submission commit and proof artifacts. Use its real hash
   in a permanent archive/release; do not cite the mutable main branch as the
   only reproducibility identifier. The appendix already lists concrete code.
5. Verify citations and the bounded scope of the prior-art claims, including
   the 2005 Section 5 assertion. The 2010 trace-norm claim from the earlier chat
   is not used in the manuscript because its exact passage was not reverified.
6. Choose one journal for formal peer review. No submission action is automated.

## Venue checks (official pages checked 20 October 2026)

Research in the Mathematical Sciences requires an abstract of 150--250 words,
4--6 keywords, MSC codes, editable LaTeX sources and PDF, and relevant
Statements and Declarations. The revised draft has an approximately 219-word
abstract (mathematics counted as tokens), six keywords, and suggested MSC2020
codes 47A55, 15A42, 68V20. Its neutral article class is suitable for an inquiry;
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

The manuscript uses paper.tex, counterexample.tex, appendix_process.tex,
references.bib, and snapshots/census_macros.tex. Keep the exact Lean artifact
and validation evidence separately accessible. A buildable manuscript-source
bundle is supplied alongside the overlay; it contains no proof-library copy.
The supplement files in this directory are preparation records, not automatic
journal attachments.
