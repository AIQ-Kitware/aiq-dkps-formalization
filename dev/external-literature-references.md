# External mathematical literature cited by this repository

**This file is not yet the centralized reference registry — it is the obvious place to start
building one.** Bibliographic data for external *mathematics* was, before this file, scattered or
absent. If you have been tasked with centralizing references, absorb the four locations listed
under "Where reference data currently lives" and then delete or redirect this file.

Scope: papers whose *mathematical content* this formalization depends on, cites, or must
eventually import. Lean formalizations by other projects are a different registry — see
[`external-lean-references.md`](external-lean-references.md).

## Where reference data currently lives

| Location | Scope |
|---|---|
| this file | external mathematical literature the Davis--Kahan campaign depends on |
| [`external-lean-references.md`](external-lean-references.md) | external *Lean* formalizations, with source commits and reuse policy |
| [`hilbert-space-operator-roadmap/references.md`](hilbert-space-operator-roadmap/references.md) | roadmap-scoped operator-theory reading |
| `papers/formalization_draft1/references.bib` | BibTeX for the paper draft only |
| `davis-kahan-1970-full-source-census.json` → `primary_source` | the primary source, with DOI |

Full texts of several of these are held locally under `non-distributable/`, which is gitignored
and intentionally not redistributed.

## Primary source

**C. Davis and W. M. Kahan**, *The Rotation of Eigenvectors by a Perturbation. III*,
SIAM J. Numer. Anal. **7**(1), 1970, 1–46. [doi:10.1137/0707001](https://doi.org/10.1137/0707001)

The maintained modernized transcription is `non-distributable/davis-kahan-1970-modernized-transcription.tex`;
the original scan is `non-distributable/DavisKahan-1970-original.pdf`. The transcription is
ground truth for section and line references throughout `dev/`, but it is a transcription:
at least one factor-of-2 defect has been located in it (see the `S2-sin-two-theta` census note),
and separately the original itself appears to carry typesetting errors (see "Known source
errata" below).

## Works Davis--Kahan cite that we must import rather than derive

### Weinberger 1960 — the eigenvector-error theorem behind (9.8)

**H. F. Weinberger**, *Error bounds in the Rayleigh--Ritz approximation of eigenvectors*,
Journal of Research of the National Bureau of Standards **64B**, 1960.
Volume record: <https://www.nist.gov/nist-research-library/journal-research-volume-64b>

Davis--Kahan invoke this in Section 9 with "Weinberger's theorem gives", and later
"the deduction follows Weinberger and Lehmann". It supplies the **angle** inequality

```
sin^2 phi_k  <=  (alphahat_k - alphacheck_k) / (gamma - alphacheck_k)
```

**Why this cannot be reconstructed from Section 9 alone.** (9.8) splits into two halves with
different status, and conflating them is a live trap:

* The *Lehmann/arrowhead lower-root* half **is** self-contained. From `T = [[D, B*],[B, C]]`
  with `dim E = 2`, `D` diagonal, `C >= gamma I`, and `B` of rank one, the comparison operator
  `Ttilde = [[D, B*],[B, gamma I]]` satisfies `T - Ttilde >= 0`; the range of `B` splits off a
  3x3 arrowhead whose two lower eigenvalues are certified lower bounds by interlacing plus
  min--max monotonicity. Rank one is not intrinsic (rank `r` gives a `(2+r)`-dimensional
  comparison); the exterior threshold is what does the work.
* The *angle* half is **not** implied by "`alphacheck_k` is some scalar lower bound for
  `lambda_k`" together with the threshold. It holds for `k = 1`, because every vector in the low
  eigenspace has Rayleigh quotient at least `lambda_1`. It **fails** for `k = 2`.

**Counterexample, worth compiling as a tripwire.** Take `T = diag(0, 10, 100)` and threshold
`gamma = 99`. There are two orthogonal Ritz vectors with Ritz values `rho_1 = 50/11 < 10` and
`rho_2 = 30`, the second being `e_2 = (1/2) f_1 + (1/sqrt 2) f_2 + (1/2) f_3`, whose squared
distance from `F = span{f_1, f_2}` is exactly `1/4`. The perfectly valid lower bound
`alphacheck_2 = 10 = lambda_2` gives `(30 - 10)/(99 - 10) = 20/89 < 1/4`, so the inequality
fails. The reason is that `P_F e_2` carries an `f_1`-component lying below `alphacheck_2`.

Weinberger's bounds satisfy a **coupled variational condition strictly stronger than independent
scalar eigenvalue lower bounds**, and Davis--Kahan suppress that machinery. Closing the angle
half therefore means either reproducing the specialized `m = 2` Weinberger argument with its
actual coupled hypotheses, or formalizing the 1960 theorem. It is not Davis--Kahan's own
mathematics, and a census row should not be marked exact on the strength of the arrowhead half
alone.

### Lehmann

Cited jointly with Weinberger for the same deduction. The optimality claim in Section 9 — that
the arrowhead's lower eigenvalues are the *best* lower bounds obtainable from the Ritz matrix,
the residual Gram matrix and the exterior threshold — is the Lehmann half. Full bibliographic
data still to be pinned down; record it here when someone has it in hand.

## Related literature held locally

Under the gitignored `non-distributable/`:

* **C. Davis**, *The rotation of eigenvectors by a perturbation* (1963) — the predecessor paper.
* **R. A. Horn and C. R. Johnson**, *Matrix Analysis* — general majorization and
  unitarily-invariant-norm background.
* **Y. Yu, T. Wang and R. J. Samworth** (2014/2015), *A useful variant of the Davis--Kahan
  theorem for statisticians* — the source for the `FinishYuWangSamworth` library; that library
  additionally maintains its own `CitationSurface.lean`.

## Known source errata

Recorded here so they are not silently propagated. Both were identified during the 2026-08-08
completion campaign and should be checked against `non-distributable/DavisKahan-1970-original.pdf`
before being described as errors in the *original* rather than in our transcription.

1. **Section 7, after `H - XHX`.** With `H = [[H_0, B*],[B, H_1]]` and `X = 2P - I`, one has
   `H - XHX = [[0, 2B*],[2B, 0]]`. The printed residual inequality that follows is written with
   `B, B*` rather than `2B, 2B*`, yielding a factor-one estimate. The Section 2 theorem statement
   carries the mathematically consistent `delta * ||sin 2Theta_0|| <= 2 ||R||`, which is the
   constant to keep. Our transcription reproduces the defect at lines 2331--2339 and 2342,
   inconsistently with its own line 758.
2. **Section 3, the Theorem 3.1 realization matrix.** The printed `Q` shows a minus sign in the
   upper-right entry against a positive lower-left entry, which is not self-adjoint. With the
   direct rotation `U` printed immediately above and `Q = U P U*`, the sign must be positive:
   `Q = [[C_0^2, C_0 S_0 J_0*], [J_0 S_0 C_0, S_1^2]]`. The minus belongs to the second column of
   `U`, not to the outer product defining `Q`.
   **Confirmed by the compiler 2026-08-09.**
   `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.HalmosAngleDatum.starProjection_targetSubspace_apply`
   (`DavisKahan/Geometry/Halmos/Realization.lean`) computes the block matrix of the realized `Q`
   as a genuine `Submodule.starProjection`, so self-adjointness is structural rather than assumed,
   and both off-diagonal entries come out positive exactly as above.
