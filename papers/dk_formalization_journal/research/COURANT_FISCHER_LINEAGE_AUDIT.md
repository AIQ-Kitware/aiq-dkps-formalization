# Courant--Fischer and Weyl: proof-lineage audit

Checked 28 October 2026 in response to the author's review. This record
supports the Courant--Fischer/Weyl attribution specifically; other theorem
families require their own evidence.

## Conclusion

The formalization was developed in this DKPS repository on Mathlib's spectral
and finite-dimensional linear-algebra foundations, then ported and adapted
into Tau Ceti through [PR #13599](https://github.com/TauCetiProject/TauCeti/pull/13599).
The accepted source preserves Kitware copyright and attributes the work to
Jon Crall, Claude Fable 5, and Claude Opus 4.8. The model names here are the
historical labels recorded in the commits and headers.

The direction is **local formalization → upstream adaptation → local
consumption of the accepted API**. This concerns the origin of formal proofs;
the underlying mathematical theorems are classical, and Mathlib supplied the
eigenvalues and orthonormal eigenbasis. Spectra ancestry is recorded for the
separate measure/calculus work, not for this Courant--Fischer cluster.

## Immutable source chain

| Stage | Evidence | What it establishes |
| --- | --- | --- |
| Initial real-space proof, 11 June 2026 | [DKPS `3b95d23e9`, `Acharyya2025/Weyl.lean`](https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/3b95d23e9af0e57e35547251e8b5a80de2ec41a1/Acharyya2025/Weyl.lean) | Both min--max directions and the Weyl bound were developed here using Mathlib. The header records Claude Fable 5. |
| Reusable real/complex donor, 11 June 2026 | [DKPS `9b69db43b`, `ForMathlib/.../CourantFischer.lean`](https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/9b69db43b780b262e10b694040fda8c6ce9a601b/ForMathlib/Analysis/InnerProductSpace/CourantFischer.lean) | The reusable proof was extracted here and local consumers were migrated. |
| Tau Ceti staging and API redesign, 24 July 2026 | [Staging `6b04bbb42`](https://github.com/AIQ-Kitware/aiq-dkps-formalization/commit/6b04bbb42690d08b4f9641af2c25a896a68f82f4), [redesign `aaf9d1405`](https://github.com/AIQ-Kitware/aiq-dkps-formalization/commit/aaf9d14052fa450d9247918a09b0fec827595eba) | The local `ForTauCeti` API includes the characteristic supremum--infimum equality. That equality was not present as an endpoint in the first June file. |
| Pre-port donor, 8 August 2026 | [DKPS `df78246f9`, `ForTauCeti/.../CourantFischer.lean`](https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/df78246f965881705c9301f96feddc270c98ceb1/ForTauCeti/Analysis/InnerProductSpace/CourantFischer.lean) | This comparison snapshot predates the October upstream PR. Its existence avoids relying on a possible later copy back from upstream. |
| Accepted port, 9 October 2026 | [PR #13599](https://github.com/TauCetiProject/TauCeti/pull/13599), [accepted source at `7ebf17ba0`](https://github.com/TauCetiProject/TauCeti/blob/7ebf17ba04725c1a575ecf3d099ce0630cd949a0/TauCeti/Analysis/InnerProductSpace/CourantFischer.lean) | The PR and source explicitly identify the DKPS donor; the proof comparison below corroborates the attribution. |
| Local retirement, 21 October 2026 | [DKPS `6800d900b`](https://github.com/AIQ-Kitware/aiq-dkps-formalization/commit/6800d900b5acae42ab778e7f4c0357b1b369c8e5) | The local donor was deleted and consumers migrated to the accepted API. Its absence from the current tree does not change its origin. |

## Proof comparison

Compared the August donor with the accepted October file, including their
finite-dimensional real/complex contexts. These declaration statements and
proof texts match after removing whitespace and line comments and accounting
for the moved dimension helper's qualification:

| Mathematical result | Declaration | Observed adaptation |
| --- | --- | --- |
| Upper min--max direction | `exists_unit_vector_re_inner_le_eigenvalue` | The eigenbasis/dimension proof is preserved; the helper becomes `Submodule.inf_ne_bot_of_finrank_lt`. |
| Lower min--max direction | `exists_submodule_forall_unit_eigenvalue_le_re_inner` | The witness span and quadratic-form proof are preserved. |
| Supremum--infimum equality | `eigenvalues_eq_iSup_iInf_re_inner` | The bounded-infimum argument and use of both directions are preserved. |
| Eigenvalue monotonicity | `eigenvalue_mono` | The min--max proof is preserved. |
| Pointwise Weyl bound | `abs_eigenvalue_sub_eigenvalue_le` | The symmetric two-sided argument is preserved; its public namespace moves from `TauCeti` to `LinearMap.IsSymmetric`. |
| Operator-norm Weyl bound | `abs_eigenvalue_sub_eigenvalue_le_norm` | The operator-norm specialization is preserved, with the same namespace move. |

The port reorganizes helpers, exposes some general eigenbasis facts, and moves
the dimension-intersection helper into the second changed file,
`TauCeti/LinearAlgebra/Dimension/Submodule.lean`. This supports an adaptation
claim, not a claim that whole files are byte-identical.

The October pre-retirement donor was also checked. Relative to the August
snapshot it changes the basis-span import to its accepted upstream location
and expands one `rwa` into `rw` plus `assumption`. The August snapshot is the
primary evidence for the direction of proof descent.

## Integration evidence and snapshot limits

The live PR reports `closed`, a `[Merged by Bors]` title, and `merged=false`.
Integration is corroborated independently: GitHub's
[commit comparison](https://github.com/TauCetiProject/TauCeti/compare/7ebf17ba04725c1a575ecf3d099ce0630cd949a0...b3de655482f7b86c77d8982566e5a73801fd64fa)
reports the manifest pin as ahead of the accepted commit, with that accepted
commit itself as the merge base. Closure alone was not used as evidence of
integration.

The local Tau Ceti checkout is shallow. Its local ancestry test stops at the
21 October boundary and cannot establish the earlier ancestry; a negative
local result here is not evidence of unrelated history. The remote comparison
supplies that missing observation. Do not attribute a file's introduction to
the shallow boundary merely because `git log --follow` stops there.

The manifest pin is `b3de655482f7b86c77d8982566e5a73801fd64fa`; the materialized
checkout is `efded067c28ffca3483fd731674eb13b42543fbb`. Both contain the same
Courant--Fischer file blob, `dd79c7da31fdd04382027082bd7dfb7d657c9036`.
The accepted PR file has blob `ed4cce28b669a0512f129017a24eba3d699f0bcd`.
The later file adds `LinearMap.sq_norm_apply_eq_sum_of_eigenbasis`; its proof
origin is not inferred from its location in the same file. No dependency
revision was changed for this audit.

## Attribution boundaries and reproduction

- Mathlib's eigenvalue/eigenbasis results are prerequisites. This audit does
  not reattribute them to DKPS.
- The donor records Spectra influence as “none.” Its imports include Mathlib
  and the local basis-span helper; the older explanatory phrase “imports only
  Mathlib” is stale after helper extraction. The local source chain supports
  the proof origin independently of that phrase.
- The donor mentions a related Weyl endpoint in the statistical-learning
  formalization. That reference does not claim this proof was copied from it;
  no exclusive first-formalization claim is made here.
- No Lean declarations were modified and no new compiler certification is
  claimed by this source/provenance audit.

To inspect the proof snapshots with the available local Git objects:

```bash
git show df78246f965881705c9301f96feddc270c98ceb1:ForTauCeti/Analysis/InnerProductSpace/CourantFischer.lean
git -C .lake/packages/TauCeti show 7ebf17ba04725c1a575ecf3d099ce0630cd949a0:TauCeti/Analysis/InnerProductSpace/CourantFischer.lean
```

Use the immutable links if those objects are unavailable. The upstream
header's link to the donor on DKPS `main` is now stale because the donor was
retired; the pinned August link above preserves access to the source.
