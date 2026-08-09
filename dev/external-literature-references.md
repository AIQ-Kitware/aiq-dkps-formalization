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
completion campaign as *candidates*, and both were checked page-by-page against
`non-distributable/DavisKahan-1970-original.pdf` on 2026-08-09. **One was confirmed in the
published original; the other was withdrawn — it never existed.** Do not reintroduce the
withdrawn one: the reasoning that produced it is plausible and will recur.

### 1. Section 7, the residual form of the sin 2theta proof — CONFIRMED, in the published original

**Original, page 34** (SIAM J. Numer. Anal. 7(1), 1970). Immediately after (7.5), the paper writes
"To get the other conclusion, we rewrite the first inequality in (7.5) in the form"

```
delta * || [[0, -sin 2Theta_0 J_0*], [J_0 sin 2Theta_0, 0]] ||  <=  || [[0, B*], [B, 0]] ||
```

"and invoke Lemma 6.1; `delta ||sin 2Theta_0|| <= ||B|| <= ||R||`. This completes the proof."

The factor of 2 is missing on the right. Section 7 sets `A + H ~= [[A_0+H_0, B*],[B, A_1+H_1]]`
at (6.3) and `A + XHX ~= [[A_0+H_0, -B*],[-B, A_1+H_1]]` at (7.1), so

```
H - XHX = [[0, 2B*], [2B, 0]],   hence  ||H - XHX|| = 2 || [[0, B*],[B, 0]] ||
```

and the rewrite must carry `2B, 2B*`. The correct conclusion is
`delta ||sin 2Theta_0|| <= 2||B|| <= 2||R||`.

**The paper contradicts itself two lines later**, which is the decisive evidence that the printed
chain is a slip rather than a sharper result: the very next paragraph reads "the inference
`delta ||sin 2Theta_0|| <= 2||R||` is valid only when `delta` pertains to gaps in the spectrum of
`Lambda`", and its counterexample computes "then surely `2||R|| = 2`". The paper treats `2||R||`
as what it just proved. The Section 2 theorem statement also carries
`delta ||sin 2Theta_0|| <= 2||R||`.

**`2` is the constant to keep.** Our transcription reproduces the original faithfully here
(lines 2331--2342), so this is *not* a transcription defect — the inconsistency is the paper's own,
between its Section 2 statement and its Section 7 proof line.

### 2. Section 3, the Theorem 3.1 realization matrix — WITHDRAWN, no such error

A 2026-08-08 campaign note claimed the printed `Q` carried a minus sign in the upper-right entry
against a positive lower-left entry, and was therefore not self-adjoint. **That claim is false.**

**Original, page 14.** Equation (3.6) prints the direct rotation
`U ~= [[C_0, -S_0*], [S_0, C_1]]`, `C_j >= 0`, and (3.7) prints

```
Q = U P U^{-1} ~= (C_0; S_0)(C_0  S_0*) = [[C_0^2, C_0 S_0*], [S_0 C_0, S_0 S_0*]]
```

Both off-diagonal entries are positive; the matrix is self-adjoint as printed. The minus sign
occurs only in the second column of `U` at (3.6), which is correct there. Our transcription
reproduces both displays faithfully.

The independently derived block matrix in
`TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.HalmosAngleDatum.starProjection_targetSubspace_apply`
(`DavisKahan/Geometry/Halmos/Realization.lean`) computes `Q` as a genuine `Submodule.starProjection`
and likewise yields both off-diagonal entries positive — agreeing with the source, not correcting it.

**Why this false positive is worth recording.** The `Q_- = XQX` display appearing shortly after
(3.7) *does* carry two minus signs, `[[C_0^2, -C_0 S_0*], [-S_0 C_0, S_0 S_0*]]`, and is also
self-adjoint. Reading a mixed-sign matrix out of that neighbourhood is an easy slip. Check
page 14 of the scan before asserting a sign defect in Section 3 again.
