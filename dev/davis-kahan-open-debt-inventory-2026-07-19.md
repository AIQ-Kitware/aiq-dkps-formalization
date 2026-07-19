# Davis--Kahan open-debt inventory

Date: 2026-07-19

This inventory was generated after the complete complex and real general sine-theta
source surface was compiler-accepted at commit `19e6d2fa5e5b`.  It supports the
larger goal of formalizing the full 1970 paper, but it is not a theorem-dependency
report: import reachability and textual open terms do not imply that a verified
endpoint depends on them.

## Immediate and large goals

- **Immediate goal for today:** preserve the completed full general sine-theta theorem and compile the optional natural-input extensions without regression.
- **Large goal:** complete the full general 1970 Davis--Kahan paper, including direct rotation, tangent and double-angle results, spectral selection, sharpness/equality content, and the remaining unbounded passages.

Static inventory: **205 occurrences in 42 files**. The count includes the 18 immutable challenge entries.

## Category totals

| category | occurrences | interpretation |
|---|---:|---|
| challenge | 18 | Intentional immutable exercises; never fill in place. |
| continuation-branch | 10 | Not required for sine-theta; relevant to later spectral selection work. |
| direct-rotation | 18 | Full-paper theorem family; likely high-value after sine-theta extensions settle. |
| double-angle | 5 | Full-paper theorem family. |
| finite-alternative | 12 | Useful regression and alternative proofs, not the source-general completion boundary. |
| ideal-instances | 16 | Concrete norm-family support beyond the abstract theorem. |
| sharpness-equality | 13 | Equality and optimality content needed for a full-paper claim. |
| spectral-projection-foundation | 36 | Potentially reusable foundations; first separate live dependencies from obsolete scaffolds. |
| superseded | 31 | Legacy infrastructure bypassed by the trusted sine-theta chain. |
| sylvester-alternatives | 9 | Older or alternative Sylvester paths; audit before proof work. |
| tan-theta | 13 | Full-paper theorem family. |
| unclassified | 24 | Needs theorem-level triage before assigning work. |

## File-level inventory

### challenge

| count | file | source-root import reachable | note |
|---:|---|---|---|
| 4 | `Challenge/MathlibPending/DavisKahanPartIII/Conformance.lean` | no | intentional immutable exercise |
| 2 | `Challenge/MathlibCandidate/DavisKahan/Conformance.lean` | no | intentional immutable exercise |
| 2 | `Challenge/MathlibPending/DavisKahanProjectorDifference/Conformance.lean` | no | intentional immutable exercise |
| 2 | `Challenge/MathlibPending/DavisKahanSylvesterPiOverTwo/Conformance.lean` | no | intentional immutable exercise |
| 1 | `Challenge/MathlibPending/Davis1963Rotation/Conformance.lean` | no | intentional immutable exercise |
| 1 | `Challenge/MathlibPending/DavisKahanSharp/Conformance.lean` | no | intentional immutable exercise |
| 1 | `Challenge/MathlibPending/DavisKahanSinTheta/Conformance.lean` | no | intentional immutable exercise |
| 1 | `Challenge/MathlibPending/DavisKahanSinTwoTheta/Conformance.lean` | no | intentional immutable exercise |
| 1 | `Challenge/MathlibPending/DavisKahanTanTheta/Conformance.lean` | no | intentional immutable exercise |
| 1 | `Challenge/MathlibPending/DavisKahanTanTwoTheta/Conformance.lean` | no | intentional immutable exercise |
| 1 | `Challenge/MathlibPending/MatrixConcentration/Conformance.lean` | no | intentional immutable exercise |
| 1 | `Challenge/MathlibPending/YuWangSamworth/Conformance.lean` | no | intentional immutable exercise |

### continuation-branch

| count | file | source-root import reachable | note |
|---:|---|---|---|
| 9 | `DavisKahan/Experimental/InfiniteDimensional/SinTheta/ContinuationRoadmap.lean` | no | candidate work for the full-paper roadmap |
| 1 | `DavisKahan/Experimental/InfiniteDimensional/SinTheta/Continuation.lean` | yes | candidate work for the full-paper roadmap |

### direct-rotation

| count | file | source-root import reachable | note |
|---:|---|---|---|
| 12 | `DavisKahan/Experimental/FiniteDimensional/DirectRotation.lean` | yes | candidate work for the full-paper roadmap |
| 6 | `DavisKahan/Experimental/InfiniteDimensional/DirectRotation.lean` | yes | candidate work for the full-paper roadmap |

### double-angle

| count | file | source-root import reachable | note |
|---:|---|---|---|
| 4 | `DavisKahan/Experimental/InfiniteDimensional/DoubleAngle.lean` | yes | candidate work for the full-paper roadmap |
| 1 | `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/SinTheta.lean` | yes | candidate work for the full-paper roadmap |

### finite-alternative

| count | file | source-root import reachable | note |
|---:|---|---|---|
| 5 | `DavisKahan/Experimental/FiniteDimensional/Core/AngleOperators.lean` | yes | candidate work for the full-paper roadmap |
| 4 | `DavisKahan/Experimental/FiniteDimensional/Generalized.lean` | yes | candidate work for the full-paper roadmap |
| 2 | `DavisKahan/Experimental/FiniteDimensional/Residual/AngleEmbeddings.lean` | yes | candidate work for the full-paper roadmap |
| 1 | `DavisKahan/Experimental/FiniteDimensional/Norms/Rectangular.lean` | yes | candidate work for the full-paper roadmap |

### ideal-instances

| count | file | source-root import reachable | note |
|---:|---|---|---|
| 8 | `DavisKahan/Experimental/InfiniteDimensional/Ideals/Symmetric.lean` | yes | candidate work for the full-paper roadmap |
| 5 | `DavisKahan/Experimental/InfiniteDimensional/Ideals/Rectangular.lean` | yes | candidate work for the full-paper roadmap |
| 3 | `DavisKahan/Experimental/InfiniteDimensional/Ideals/CompactAndSingular.lean` | yes | candidate work for the full-paper roadmap |

### sharpness-equality

| count | file | source-root import reachable | note |
|---:|---|---|---|
| 9 | `DavisKahan/Experimental/FiniteDimensional/Sharpness.lean` | yes | candidate work for the full-paper roadmap |
| 4 | `DavisKahan/Experimental/InfiniteDimensional/Sharpness.lean` | yes | candidate work for the full-paper roadmap |

### spectral-projection-foundation

| count | file | source-root import reachable | note |
|---:|---|---|---|
| 16 | `DavisKahan/Experimental/InfiniteDimensional/Core/SpectralProjection.lean` | yes | candidate work for the full-paper roadmap |
| 15 | `DavisKahan/Experimental/InfiniteDimensional/Core/OperatorAngle.lean` | yes | candidate work for the full-paper roadmap |
| 5 | `DavisKahan/Experimental/InfiniteDimensional/Core/Forms.lean` | yes | candidate work for the full-paper roadmap |

### superseded

| count | file | source-root import reachable | note |
|---:|---|---|---|
| 31 | `DavisKahan/Experimental/InfiniteDimensional/Core/UnboundedSpectral.lean` | yes | legacy cutoff facade bypassed by the direct Spectra engine |

### sylvester-alternatives

| count | file | source-root import reachable | note |
|---:|---|---|---|
| 5 | `DavisKahan/Experimental/InfiniteDimensional/Sylvester/Resolvent.lean` | yes | candidate work for the full-paper roadmap |
| 4 | `DavisKahan/Experimental/InfiniteDimensional/Sylvester/Basic.lean` | yes | candidate work for the full-paper roadmap |

### tan-theta

| count | file | source-root import reachable | note |
|---:|---|---|---|
| 7 | `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/TanTheta.lean` | yes | candidate work for the full-paper roadmap |
| 6 | `DavisKahan/Experimental/FiniteDimensional/TanTheta/GraphOperator.lean` | yes | candidate work for the full-paper roadmap |

### unclassified

| count | file | source-root import reachable | note |
|---:|---|---|---|
| 6 | `DavisKahan/Experimental/InfiniteDimensional/Core/Unbounded.lean` | yes | requires theorem-level triage |
| 6 | `DavisKahan/Experimental/InfiniteDimensional/OperatorBlocks/OffDiagonal.lean` | yes | requires theorem-level triage |
| 5 | `DavisKahan/Experimental/InfiniteDimensional/SinTheta/General.lean` | yes | requires theorem-level triage |
| 4 | `DavisKahan/Experimental/InfiniteDimensional/SinTheta/SpectralBridge.lean` | yes | requires theorem-level triage |
| 1 | `DavisKahan/Experimental/InfiniteDimensional/Core/AbstractSpectrum.lean` | yes | requires theorem-level triage |
| 1 | `DavisKahan/FiniteDimensional/Sylvester/Internal/ReciprocalMultiplier.lean` | yes | requires theorem-level triage |
| 1 | `DavisKahan/Specialized/SingularSubspace.lean` | no | requires theorem-level triage |

## Recommended next triage

1. Keep `Core/UnboundedSpectral.lean` quarantined; the completed sine-theta path intentionally bypasses it.
2. Build a declaration-level inventory for direct rotation, tangent-theta, double-angle, and sharpness before assigning proof work.
3. Separate files whose open declarations are imported but unused from files containing obligations on a desired source endpoint.
4. Decide whether `FullPartIII` should become an explicit CI target. Do not broaden the default root without a maintainer decision.
5. Treat the real-complexification instance diamond as a separate foundational design ticket, not as part of theorem completion.

## Reproduction

```bash
python scripts/inventory_davis_kahan_debt.py --write-json dev/davis-kahan-open-debt-inventory-2026-07-19.json
```
