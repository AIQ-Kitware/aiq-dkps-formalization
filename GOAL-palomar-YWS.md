You are doing the final adversarial correction pass on the Yu–Wang–Samworth
2015 Palomar preparation.

STARTING COMMIT:

    38e2a176fcf4ddec86d0ea9e5cdfcec6852f0927

Do NOT submit or register anything with Palomar.

The current work is close, but it is NOT yet ready for submission. An
independent adversarial review found both a current Palomar mechanical metadata
failure and substantive source-alignment problems in the rectangular Theorem 3
entry.

Your task is to fix those problems without weakening the mathematics or
changing the theorem merely to satisfy packaging.

======================================================================
FIRST: REFRESH THE AUTHORITATIVE SOURCES
======================================================================

Before editing, re-read:

1. the current PalomarPolicy CONTRIBUTING.md on `main`;
2. the current Palomar submission instructions/template;
3. the published Biometrika 2015 Yu–Wang–Samworth paper, not merely the
   arXiv/preprint numbering;
4. `palomar/YWS_SOURCE_CONTRACT.md`;
5. the production paper-facing YWS theorem declarations.

Record the exact Palomar policy commit consulted.

Do not trust this prompt over a newer Palomar policy if they conflict. Report
any conflict rather than guessing.

======================================================================
BLOCKER 1: FIX THE CURRENT PALOMAR METADATA SCHEMA FAILURE
======================================================================

Current root `formalization.yaml` has:

    sources:
      ...
      type: article

Current Palomar policy only accepts source types:

    paper
    book
    web discussion
    folklore
    original-proof
    other

Change the YWS source type to:

    type: paper

Then validate the file with the CURRENT official Palomar metadata/preflight
tooling, not only a generic YAML parser.

Also review every other enum against current policy.

======================================================================
BLOCKER 2: RESTORE THE PAPER'S `s <= rank(A)` HYPOTHESIS IN THEOREM 3
======================================================================

This is a real source-fidelity defect in the current Palomar Challenge.

Published Theorem 3 says:

    1 <= r <= s <= rank(A)

The Challenge currently requires only:

right:
    s < q

left:
    s < p

That allows selected blocks in the zero-singular-value tail beyond rank(A).
The resulting theorem may be a valid generalization, but it is NOT the
source-corrected Theorem 3 at the paper's stated scope.

The Palomar theorem is supposed to be the paper-facing result, so restore the
source rank condition.

Because Challenge indices are zero-based, express the paper condition
appropriately, e.g. conceptually:

    s < finrank ℝ (LinearMap.range A)

or an equivalent standard Mathlib finite-rank formulation.

Do not merely add it as an unused redundant hypothesis without checking the
index translation.

From that source condition derive internally:

    s < q
    s < p
    q > 0
    p > 0

as appropriate.

In particular, the current caller-visible

    hq : 0 < q

on the left Theorem 3 declarations should disappear if it follows from the
source rank condition.

Apply the corrected rank condition to all four compared declarations:

    theorem3_rightSinTheta
    theorem3_rightAlignedFrame
    theorem3_leftSinTheta
    theorem3_leftAlignedFrame

Do this first in the production/source-facing YWS API if the corresponding
production theorem wrappers are currently broader than the paper.

KEEP the broader existing theorems if they are useful. They can remain
generalized lower-level results.

Add new canonical paper-facing/corrected-source wrappers rather than weakening
or deleting useful generalizations.

======================================================================
BLOCKER 3: THEOREM 3 MUST USE THE EXACT CORRECTED SOURCE DENOMINATOR
======================================================================

The current Challenge defines:

    SingularBoundaryGap ... Delta

as only:

    Delta <= upper boundary gap
    Delta <= lower boundary gap

and then quantifies over any positive `Delta`.

The published theorem instead uses:

    Delta_sv =
      min(
        sigma_{r-1}^2 - sigma_r^2,
        sigma_s^2 - sigma_{s+1}^2
      )

with endpoint conventions.

This exact-vs-lower-bound distinction was already identified and fixed for
Theorem 2 using `SourcePopulationGap`.

Do the analogous job for Theorem 3.

Create a small source-facing predicate, name along the lines of:

    SourceSingularGap

that identifies `Delta` with the exact corrected finite denominator, rather
than merely requiring it to be a lower bound.

Use the corrected AMBIENT endpoint convention established by the formalization
and by the paper's proof:

right singular block:
    ambient Gram dimension = q

left singular block:
    ambient Gram dimension = p

At indices beyond rank(A), ordinary singular values are zero.

The false printed convention

    sigma^2_{rank(A)+1} := -infinity

must NOT be reintroduced.

The resulting source-facing statement should have BOTH:

    the paper's source condition s <= rank(A)
    the corrected ambient endpoint convention

These are separate issues.

Handle endpoint cases precisely.

For a right block:
- r at the first source index means the upper boundary is +infinity;
- if a selected rank block ends before ambient q, the next Gram eigenvalue is
  the ordinary next squared singular value, possibly zero;
- if the full right ambient space is selected and A has full column rank, the
  lower endpoint is +infinity under the Theorem-2 ambient convention.

Analogously on the left with ambient p.

Do not lie by saying a finite `Delta` "is infinity".

If the full ambient-space case has both source boundaries infinite, either:

A. encode it explicitly as a separate disjunct, with the theorem available for
   every positive finite Delta because the sine distance is identically zero;

or

B. give a similarly transparent endpoint encoding.

Whichever route you choose, document it accurately.

Then use `SourceSingularGap`, not merely `SingularBoundaryGap`, in all four
Palomar Theorem 3 declarations.

Keep `SingularBoundaryGap` as an internal proof-engine predicate if useful.

Prove the adapter from the exact source predicate to the lower-bound hypotheses
consumed by the current perturbation theorem.

======================================================================
BLOCKER 4: FIX THE FALSE FIVE-BY-FIVE EXAMPLE
======================================================================

Current files say:

    Sigma    = diag(50,40,30,20,10)
    SigmaHat = diag(54,37,32,23,21)
    r = s = 4

and claim the classical mixed separation is zero.

That is wrong.

The published paper's example selects the second, third and fourth largest
eigenvalues:

    r = 2
    s = 4

in the paper's ONE-BASED indexing.

Fix every occurrence, including at least:

    Palomar/YWSSymmetric/Challenge.lean
    README.md
    formalization.yaml if the index choice is stated there
    source-contract prose
    any tests/examples derived from this wording

Be very explicit about one-based paper indices versus zero-based Lean indices.

If a Lean executable regression theorem represents this example, verify its
actual block indices as well rather than changing prose only.

======================================================================
BLOCKER 5: ENTRY-SPECIFIC SOURCE RELATIONSHIPS
======================================================================

The current root metadata says:

    relationship: formalizes

for the YWS paper.

That is appropriate for the source-exact symmetric entry.

It is NOT the right description for the rectangular entry because Theorem 3
changes a false printed convention.

Current Palomar vocabulary says:

    formalizes = formalizes the source result
    adapts     = changes or extends the source result

Prepare entry-specific metadata if current Palomar supports the explicit
metadata path, preferably:

    palomar/yws-symmetric/formalization.yaml
    palomar/yws-rectangular/formalization.yaml

For the symmetric entry:

    relationship: formalizes

For the rectangular Theorem 3 entry:

    relationship: adapts

The rectangular source note must say exactly what is changed:

- printed `sigma^2_{rank(A)+1} := -infinity` is false;
- a compiled counterexample exists;
- the formal theorem uses the ambient Gram-spectrum convention dictated by the
  proof through A^T A / A A^T;
- the source condition `s <= rank(A)` is nevertheless retained.

Do not call the rectangular theorem exact.

If current Palomar metadata selection works differently, follow current policy,
but preserve this semantic distinction.

======================================================================
BLOCKER 6: REMOVE FALSE PROJECT-WIDE CLAIMS ABOUT SAMPLE GAPS
======================================================================

Current `formalization.yaml` says:

    "No sample eigengap is assumed anywhere"

That is false project-wide because Theorem 1 is the classical mixed
population/sample separation theorem.

Replace it with something accurate, e.g.:

    "Theorem 2 and Corollary 1 require only population eigengaps; the corrected
    Theorem 3 similarly uses only population singular-value gaps. No sample
    eigengap appears in those results."

The Challenge prose currently also says:

    "Every hypothesis constrains Sigma alone."

That is literally false because:
- SigmaHat is assumed symmetric;
- the supplied sample frame satisfies SigmaHat eigenvector equations.

The important mathematical claim is:

    every SEPARATION/GAP hypothesis uses only Sigma.

Rewrite both the Challenge and README accordingly.

Search the entire repo for equivalent overstatements.

======================================================================
BLOCKER 7: FIX THE "EVERY RESULT AT PRINTED GENERALITY" CONTRADICTION
======================================================================

README currently says:

    "Every numbered result of the paper, at the printed generality"

and then immediately documents that Theorem 3 is false as printed and repaired.

Rewrite this.

A good shape is:

    "Every numbered result is represented in the development. Theorem 2 and
    Corollary 1 have source-exact paper-facing statements; Theorem 3 is a
    documented correction of a false printed boundary convention; Theorem 1
    and Appendix Lemma A1 have the dispositions described below."

Do not use one blanket adjective for heterogeneous source dispositions.

Review the root project description for the same problem.

======================================================================
POLISH 1: FIX THE FULL-BLOCK `SourcePopulationGap` DESCRIPTION
======================================================================

The current predicate is mathematically reasonable, but its docstring
overstates it.

Outside the full-block case, it identifies the exact finite source
denominator.

In the full-block case, the source convention has both exterior gaps infinite,
while Lean accepts any positive finite Delta as a surrogate because the selected
subspace is the entire space and the conclusion is trivial.

Say exactly that.

Do not say:

    "`Delta` here is the paper's denominator itself"

without qualifying the full-space endpoint case.

Consider whether a direct zero-conclusion full-space branch would make the
statement even cleaner, but do not add complexity merely for aesthetics.

======================================================================
POLISH 2: HOSTILELY AUDIT THE SINGULAR-FRAME DEFINITIONS
======================================================================

Current Challenge defines a right singular block through:

    A^T A v_i = sigma_i^2 v_i

and the left block through:

    A A^T u_i = sigma_i^2 u_i

while the paper writes paired singular-vector equations:

    A v_j = sigma_j u_j
    A^T u_j = sigma_j v_j

Once `s <= rank(A)`, every selected sigma_j is positive, so the Gram-eigenvector
form should be equivalent to the ordinary singular-vector interpretation.

Do not merely assume that.

Prove a short production/bridge theorem establishing the source equivalence at
the selected positive-rank indices.

Then decide which representation gives the cleaner Challenge:

A. keep the Gram-eigenvector version, with a docstring and compiled equivalence
   to the paper's singular-vector condition; or

B. state the paired singular-vector condition literally if it stays concise.

Do not enlarge the trusted statement for cosmetic source mimicry if the
standard equivalent Gram characterization is cleaner, but make the equivalence
machine-checked.

======================================================================
POLISH 3: REGENERATE `YWS_SOURCE_CONTRACT.md`
======================================================================

Do not patch only the final table.

Re-audit it from the actual final theorem types.

It currently contains stale material from earlier states, including old
Corollary/denominator and aligned-frame descriptions, and it explicitly records
the Theorem 3 exact-gap mismatch while later calling the entry selected.

For every compared theorem record:

- exact published result number;
- source one-based block;
- Challenge zero-based block;
- source rank restriction;
- exact denominator;
- endpoint convention;
- sample-gap status;
- arbitrary-frame status;
- numerator and constant;
- aligned conclusion;
- source disposition;
- production theorem used by Solution.

The final contract must not contain any known contradiction.

======================================================================
POLISH 4: VERIFY AUTHORSHIP BEFORE PUBLISHING IT
======================================================================

Current Palomar files and metadata name:

    Jon Crall
    Edward Wang

The extracted git history and ordinary YWS module headers visible in this
repository primarily attribute the formalization to Jon Crall plus named AI
systems.

That does not prove Edward Wang is not an author; contribution evidence may
exist elsewhere.

But Palomar publishes authorship.

Before finalizing metadata:

- locate concrete contribution/provenance evidence for Edward Wang;
- if the maintainer confirms the authorship, retain it;
- otherwise remove it;
- do not infer formalization authorship from mathematical-paper authorship or
  organizational association.

Record this as a HUMAN REVIEW ITEM if it cannot be adjudicated from repository
evidence.

Do not invent an answer.

======================================================================
POLISH 5: VERIFY AUTOMATION DISCLOSURE
======================================================================

Current metadata groups GPT and Claude models under:

    framework: Claude Code

Check that this is historically accurate.

If GPT-based work used a different framework/product, split the automation
records or use a neutral accurate framework description.

Do not manufacture per-model cost/timing data.

======================================================================
POLISH 6: REPOSITORY ROLE / EXTRACTION PROVENANCE
======================================================================

Current metadata explicitly says:

    repository:
      role: substantive-development

while README says this repository is an extraction and the larger
aiq-dkps-formalization repository remains authoritative.

Current Palomar policy says:
- omit `repository` for an ordinary substantive development;
- use `repository.substantive_formalization` with exact public repo + SHA for a
  thin wrapper.

Decide what this repository ACTUALLY is.

The extraction physically contains the proof source, so treating it as a
substantive development may be reasonable even if another repo is the canonical
development location.

If so:
- preferably omit the legacy explicit `repository.role`;
- accurately describe the extraction lineage and authoritative upstream in
  README / related formalization metadata.

If this repo is intended only as a packaging wrapper around the larger repo,
then use the current thin-wrapper metadata shape with an exact public
substantive repository and 40-character revision.

Do not leave the relationship conceptually ambiguous.

======================================================================
POLISH 7: `definition_names`
======================================================================

Current configs put fully specified Challenge helper definitions in
`definition_names`.

Current Palomar documentation describes `definition_names` as definitions whose
values are left unspecified in the Challenge and supplied by Solution.

Do not guess about Comparator behavior.

Using the CURRENT official Comparator / Palomar tooling, determine whether these
fully specified helper definitions should:

- be omitted from `definition_names`, because theorem comparison unfolds or
  independently sees them; or
- remain because Comparator needs them explicitly compared.

If they remain, document why this is valid under the current tool.

Do not make a previously explicit ordinary mathematical definition opaque merely
to justify `definition_names`.

======================================================================
THEOREM 2 / COROLLARY 1 REGRESSION AUDIT
======================================================================

The symmetric entry is close to submission quality. Protect that work.

After edits, adversarially confirm:

THEOREM 2:
- real symmetric p x p matrices;
- source block 1 <= r <= s <= p;
- arbitrary supplied population eigenframe;
- arbitrary supplied sample eigenframe;
- repeated sample eigenvalues allowed;
- NO sample eigengap;
- exact finite population denominator outside the full-space endpoint case;
- numerator is exactly:
      min(sqrt(d) * ||E||_op, ||E||_F)
- factor exactly 2;
- aligned conclusion returns O in O(d);
- aligned factor exactly 2 * sqrt(2);
- comparison is against the supplied population frame.

COROLLARY 1:
- arbitrary supplied sample eigenvector under degeneracy;
- unit normalization matches the d=1 specialization;
- exact neighbouring population denominator;
- first factor 2;
- orientation/sign condition in second display;
- second factor 2 * sqrt(2).

Keep the compiled scalar-sample degeneracy witness as a regression test.

======================================================================
THEOREM 3 FINAL ACCEPTANCE CONTRACT
======================================================================

Do not call the rectangular entry ready unless ALL of these are true:

- A, Ahat are real p x q maps;
- source block condition is exactly the zero-based equivalent of:
      1 <= r <= s <= rank(A);
- d = s - r + 1;
- supplied sample singular frame remains arbitrary under multiplicity;
- no sample singular-value gap;
- corrected population denominator is the EXACT minimum under the ambient Gram
  convention;
- printed false `rank(A)+1 := -infinity` convention is explicitly disclosed;
- right sine conclusion present;
- right aligned-frame conclusion present;
- left sine conclusion present;
- left aligned-frame conclusion present;
- coefficient is exactly:
      2 * (2 sigma_1 + ||D||_op)
        * min(sqrt(d) ||D||_op, ||D||_F)
        / Delta
  for sine;
- aligned coefficient has the additional sqrt(2), i.e. printed 2^(3/2);
- source rank condition is retained even if the lower-level theorem is more
  general;
- metadata relationship says `adapts`;
- Challenge prose calls this corrected, not exact.

======================================================================
PALOMAR MECHANICAL REVALIDATION
======================================================================

After all statement and metadata changes:

1. Check current Challenge sizes.
   Aim below 300 lines and 32 KiB.
   Do not sacrifice source fidelity merely to stay below the warning; the hard
   cap is larger.

2. Verify direct and TRANSITIVE Challenge imports.
   Both final Challenges should remain Mathlib-only unless a compelling reason
   emerges.

3. Run:
       lake build
       lake build Palomar
   and all ordinary YWS targets.

4. Run current official Palomar metadata/preflight validation.

5. Run the REAL current Comparator independently for:
       palomar/yws-symmetric/comparator.json
       palomar/yws-rectangular/comparator.json

6. Run NanoDa for both.

7. Audit axiom closure of every selected Solution theorem.
   Allowed only:
       propext
       Quot.sound
       Classical.choice

   No:
       sorryAx
       Lean.ofReduceBool
       custom axioms

8. Verify no production `sorry` outside deliberate Challenge holes.

9. Verify:
       no git submodules
       no LFS pointers
       no compiled artifacts outside .lake
       public credential-free pinned Git dependencies
       exactly one root license
       license matches metadata

10. Perform the entire verification from a CLEAN CLONE of the exact final
    candidate commit.

======================================================================
PUBLIC-COMMIT / PREVIEW CHECK
======================================================================

Palomar submission is against an exact public GitHub SHA.

Before declaring READY:

- push the final candidate commit to the intended public GitHub repository;
- verify the full 40-character SHA;
- run Palomar's preliminary checks/preview against that exact public SHA if the
  workflow permits doing so without registration;
- inspect the rendered abstract, selected declarations, source relationship,
  and warnings.

Do NOT press/register/complete the final registry action.

======================================================================
FINAL REPORT
======================================================================

Give the maintainer an adversarial report.

Start:

    BASE HEAD: 38e2a176fcf4ddec86d0ea9e5cdfcec6852f0927
    FINAL HEAD: <sha>

Then for each final entry report:

    entry
    comparator path
    metadata path
    selected declarations
    Challenge lines / bytes
    direct imports
    transitive dependency classes
    source relationship
    exact/corrected status
    Comparator
    NanoDa
    axiom audit
    clean-clone result
    public-SHA preliminary Palomar result

Include a source-vs-Challenge table for each compared theorem.

Explicitly answer:

1. Is the five-by-five example now r=2,s=4 in paper indexing?
2. Does Theorem 2 permit arbitrary sample eigenframes under degeneracy?
3. Is there no sample eigengap in Theorem 2/Corollary 1?
4. Is the Theorem 2 denominator exact outside the explicitly handled
   full-space endpoint?
5. Does Theorem 3 restore s <= rank(A)?
6. Does Theorem 3 use the exact corrected denominator rather than an arbitrary
   lower bound?
7. Is the corrected ambient endpoint convention explicit?
8. Are all four right/left sine/aligned Theorem 3 conclusions present?
9. Is the rectangular source relationship `adapts`?
10. Does current official Palomar metadata validation pass?
11. Were authorship names affirmatively verified by the maintainer/repository
    evidence?
12. Did both configs pass real Comparator + NanoDa from a clean clone?

Do not report:

    submitted
    registered
    accepted
    approved

until the maintainer actually performs that action.

The desired final status is:

    READY FOR MAINTAINER PALOMAR PREVIEW

If anything above fails, report:

    BLOCKED: <exact issue>

======================================================================
PRINCIPLE
======================================================================

Do not optimize for a green Comparator at the expense of the paper statement.

The purpose of this pass is to make the tiny trusted Challenge say exactly the
mathematics the YWS paper says where the source is correct, and exactly the
documented repaired mathematics where the source is false.

A valid generalized theorem with an omitted source hypothesis is still the wrong
Palomar statement if the entry advertises itself as the paper-facing theorem.
