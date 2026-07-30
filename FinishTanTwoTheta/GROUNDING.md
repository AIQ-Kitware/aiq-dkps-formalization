# Grounding

## Audit status, 2026-07-30 (lane CLAIM-DOC)

`python3 FinishTanTwoTheta/scripts/verify_grounding.py` → **passes**, 13 repository
source files checked, exit 0.

It did **not** pass when this lane started: four of its pinned references had gone
stale under other lanes' migrations, and nothing was running the script to notice.
None of the four was missing mathematics, and all four are repointed rather than
deleted:

| was | now | why |
|---|---|---|
| `DavisKahan/Experimental/InfiniteDimensional/Riccati/BoundedCore.lean` | `DavisKahan/Riccati/BoundedCore.lean` | `023b2ceb` promoted the bounded Riccati block out of `Experimental`, by path only |
| `DavisKahan/Sylvester/ClosedSylvesterEquation.lean` — `SemiboundedBelow.toLinearMap_bound`, `SemiboundedAbove.toLinearMap_bound` | `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean` — `def SemiboundedBelow`, `def SemiboundedAbove` | `9e10b784` deleted the two bundled wrappers as dead (zero callers; the bundled predicate is a reducible `abbrev`, so callers use the `ForTauCeti` twins by defeq) |
| `vendor/Spectra/Spectra/SpectralTheory/Algebra.lean` | `retired/Spectra/Spectra/SpectralTheory/Algebra.lean` | the Spectra snapshot moved from `vendor/` to `retired/` when the dependency was retired; this is a grounding reference to the donor, not an import |

**The script is now in `dev/README.md`'s gate list**, so the next such drift shows
up as a failing gate rather than as an unverified claim in this document. That was
the finding: a completeness claim is only worth what re-runs it.


The package distinguishes three theorem layers.

1. The main Davis--Kahan tree already supplies the finite-dimensional Section 7
   theorem and the finite-carrier ambient extension.
2. `paperTanTwoTheta_uiNorm_finite_alternate` duplicates the finite endpoint by
   a different Riccati/approximation-number route and is retained only as a
   regression proof.
3. `paperFaithful_tanTwoTheta_uiNorm` is the actual unrestricted bounded target:
   arbitrary Hilbert space, no finite carrier, a derived quarter-acute branch,
   the canonical ambient tangent, and the sharp source-ideal estimate against
   the full perturbation.

The unrestricted proof attempt is explicit and admission-free.  The branch
argument is in `InfiniteQuarterAcute`; the canonical/graph approximation-number
transport is in `CanonicalTangentBridge`; `PaperFaithful` composes those bridges
with the existing arbitrary-Hilbert post-branch Riccati/Ky-Fan theorem.

This document does **not** claim completion merely because the source is
written.  Grounding requires successful compilation of the three modules and
the aggregate, followed by an axiom audit of
`paperFaithful_tanTwoTheta_uiNorm`.  Until then the status is “complete proof
attempt ready for compiler review,” not “proved.”
