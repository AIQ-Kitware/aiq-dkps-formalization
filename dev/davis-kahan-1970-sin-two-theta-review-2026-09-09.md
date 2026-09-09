# Sin-two-theta source review and paper revision, 2026-09-09

## Verdict and validation boundary

The displayed current declaration
`TauCeti.DavisKahan1970.sinTwoTheta_unbounded_perturbedGap_whereDefinedUIN_rclike`
is **not a full-scope representation of the source theorem**. Its inequalities,
factor two, perturbed-spectrum gap, and scalar-generic real/complex treatment
are appropriate. Its trial-domain and boundedness hypotheses exclude source
inputs. The selected combined theorem also passes those restrictions to its
ambient conclusion.

The overlay includes a common-domain replacement with proof code, but **Lean
and Lake are unavailable in the review environment**. No new declaration has
been compiler-validated. The replacement is isolated from `DavisKahan.All` and
from accepted aliases. It contains no `sorry`, `admit`, or new axiom, but absence
of those tokens is not a compilation result. The result register now blocks
`S2-sin-two-theta`; it retains the other 28 decisions without independently
re-certifying them. Existing restricted theorems are not being called false.

This review compares source statements, inherited assumptions, and definitions
that affect their meaning. It does not require the Lean proofs to follow Davis
and Kahan's proof strategy. The reflection argument below explains the proposed
repair, not the standard by which the earlier theorem was rejected.

## Evidence and source boundary

The reviewed checkout is `13ea1322d4e4` from the supplied source archive.
The external comparison source is the supplied modernized transcription;
the workflow PNG is also supplied separately. The private transcription is
not copied into this distributable overlay. Input hashes are recorded below.

Relevant transcription locations (original file line numbers):

- Section 1, lines 193--237: separable real/complex Hilbert spaces, bounded or
  unbounded self-adjoint operators, domain condition, reducing subspaces.
- Section 1, lines 479--593: residual `R=H E0`, the separate Ritz specialization,
  norm conventions, and the cited Ky Fan comparison theorem.
- Section 2, lines 753--785: the perturbed-block gap and both factor-two
  inequalities; bounded `H` **or** bounded `R`; half-infinite interval extension.
- Appendix to Section 6, lines 2114--2124: common dense domain for `T E0` and
  `E0 A0`, with bounded continuous extension of the residual.
- Section 7, lines 2261--2356: reflection, ambient estimate, directed/ambient
  distinction, and the inconsistent residual proof passage discussed below.

Relevant repository declarations are in:

- `DavisKahan/Sources/DavisKahan1970/SinTwoThetaDirectedRCLike.lean`:
  the current combined statement and directed bounded-trial statements.
- `DavisKahan/Sources/DavisKahan1970/SinTwoThetaAmbientUnbounded.lean`:
  the independent ambient theorem without trial-domain hypotheses.
- `DavisKahan/Sylvester/Gap.lean`: `FormBoundedSylvesterGap`, including
  interval/exterior and both semibounded ordered cases.
- `DavisKahan/Geometry/Angle/OperatorAngleGeneric.lean`: the directed
  double sine and ambient functional-calculus angle.
- `DavisKahan/OperatorIdeal/NormalizedUnitaryInvariantNorm.lean`:
  the norm structure and its explicit where-defined Fan law.

The generated exact signature sidecars remain the existing historical and
current statements. They are source extractions, not fresh compiler output.
The paper does not replace its current display with an unvalidated candidate
and then describe it as checked.

## 1. Actual scope restriction

The current shared prefix includes a bounded `M : P ->L P`, a bounded ambient
perturbation `Hop`, and

```
hPdom : forall p : P, (p : H) belongs to domain (A + Hop)
```

The residual identity is then asserted for every trial vector. The source
allows an unbounded trial restriction. Its relevant operators have a common
**dense** domain; it is their difference that has a bounded extension. A
partial-map type on the ambient operator does not remove the stronger trial
hypothesis.

Moreover, a conjunction shares all preceding hypotheses. The current ambient
conjunct therefore cannot be applied at an input where `hPdom` fails, even
though the independent ambient theorem can. Putting two conclusions in a
single declaration did not resolve the source-scope problem.

There is a separate boundedness distinction: a useful directed residual bound
can hold when only `R` is bounded and the perturbation on the complementary
subspace is unbounded. A globally bounded `Hop` must not be imposed on that
clause merely because it is convenient for the ambient clause.

### Scope-separating examples

These are deductions from the displayed hypotheses, not examples quoted from
Davis and Kahan. Let `D(x)_n=(n+1)x_n` on its natural self-adjoint domain in
`l2(N)`; indices start at zero.

**Half-infinite gap, zero angle.** Set `A=T=(-D) direct-sum D` and let `P=Q`
select the first summand. The two perturbed spectral parts are at most `-1`
and at least `1`, so the source gap is 2. Both the perturbation and residual
are zero. But `x_n=1/(n+1)` is square summable and `Dx` is not; the first
summand is not contained in the operator domain. Thus `hPdom` fails even for
zero angle and zero perturbation.

**Finite gap interval.** Set `A=T=D direct-sum 0`, with `P` the first summand
and `Q` the second. The Q-block spectrum is `{0}`, the complementary spectrum
is contained in `[1,infinity)`, and the finite-interval gap holds with
`[beta,alpha]=[0,0]` and delta=1. The paired and crossed subspaces have the
matching infinite dimensions required by the source. The angle is pi/2, so
its double sine is zero, but `hPdom` again fails. The issue is not confined
to the half-infinite extension.

**Bounded residual without bounded perturbation.** Set
`A=(-D) direct-sum D`, `T=(-D) direct-sum 2D`, and let `P=Q` select the first
summand. The domains agree and `R=0`, while `T-A=0 direct-sum D` is unbounded.
The directed source inference applies; a globally bounded perturbation API
cannot express this input.

## 2. Proposed common-domain formalization

New module:
`DavisKahan/Sources/DavisKahan1970/SinTwoThetaCommonDomain.lean`.

Its setup consists of self-adjoint partial maps `A,T` with equal domains,
`P` reducing `A`, `Q` reducing `T`, and the source gap on the Q-blocks of `T`.
The directed clause takes a bounded residual `R : P ->L E` satisfying
`Tp=Ap+Rp` for trial vectors already in the common domain. The trial operator
is the reducing restriction of `A`; it need not be bounded. The source sum
`T=A+H`, with H defined on the domain of A, has exactly this common-domain
interpretation. The ambient clause separately quantifies over a bounded
self-adjoint `Hop` and an equality `T=addBounded A Hop`.

The new analytic lemma is `commonDomain_trialReflection_intertwines`. Write
`C=Pperp R inclusion*`, `S=C+C*`, and `J=2P-I`. Reduction of A makes P preserve
the common domain, hence J does too. On that domain the residual equation gives

```
C x  = Pperp T P x
C* x = P T Pperp x
(C-C*)x = TPx-PTx
(T-2S)Jx = JTx.
```

The adjoint identity is proved by testing against vectors in the dense domain
and using self-adjointness of T. Existing reflection/Ky Fan estimates then give
the double-angle block bound by `2 ||C||_k <= 2 ||R||_k`. Existing angle
correspondence transfers the block to the directed angle. The norm record's
where-defined Fan comparison supplies the displayed norm inequality.

The final `sinTwoTheta_commonDomain_whereDefinedUIN_rclike` places the bounded
residual hypotheses inside the directed conjunct and the bounded perturbation
hypotheses inside the ambient conjunct. The latter reuses the independent
ambient theorem. Neither conjunct requires a bounded trial block or puts all
trial vectors into the operator domain.

The occurrence of `0` in `trialOffDiagonalPart P 0 R` is a parameter to an
existing bounded-block constructor: `trialOffDiagonalBlock_eq` eliminates
that parameter and gives `Pperp R inclusion*`. It is **not** the assumption
that the trial restriction is zero or bounded.

The accompanying audit module prints the types and axioms, checks real and
complex instantiations, and calls the ambient conjunct without any residual,
bounded trial operator, or whole-trial-space domain hypothesis. These are
compiler-input checks, not checks already executed here.

## 3. Norm model: expose the actual assumption

`NormalizedSymmetricOperatorIdealFamily` is not just an ideal norm plus
rank-one normalization. It contains
`gauge_le_of_forall_kyFanApproximationGauge_le_defined`. The theorem
`hasFanDominanceWhereDefined` exposes that field. It does not prove Fan
comparison independently from the remaining record fields.

Davis--Kahan cite Fan's comparison theorem in Section 1. Packaging that
mathematical background can be a valid modeling choice, but the paper must
say which background is packaged and must not count its accessor as a new
foundation proof. The stronger unconditional extended-real version also
transfers ideal membership, a different assertion from comparison when both
norms are defined. The revised manuscript and module comments make that
boundary explicit. A claim to encompass every norm from a weaker, bare
unitary-invariance definition would additionally need a representation or
comparison theorem; this overlay does not claim to establish it.

## 4. Constant and source-transcription check

The Section 2 theorem in the supplied transcription has factor two on both
right-hand sides. Its Section 7 residual proof passage drops that factor in
the off-diagonal matrix and the following residual inequality. These cannot
both be correct.

For a direct check in R2, take unperturbed `A=0`,
`T=H=[[0,1],[1,0]]`, `P=span(e1)`, and `Q=span(e1+e2)`. The perturbed eigenvalues
are 1 and -1, the gap is 2, the angle is pi/4, and `||R||=1`. Thus
`delta sin(2 theta)=2=2||R||`, while the factor-one bound would assert `2<=1`.
Also `H-JHJ` is twice the off-diagonal part, as the reflection argument requires.

The Lean theorem's factor two is appropriate. This finding is about the
**supplied transcription**. It is not a claim that the original printed
article contains the error; that would require comparison with the scan.
The overlay does not alter the private source.

## 5. Manuscript corrections

The revised abstract and conclusion distinguish the 29-target artifact count
from a claim of full mathematical correspondence. The current restricted
signature remains visible as a second example of a statement-level mismatch.
The proposed common-domain repair is explained in the appendix and explicitly
marked unvalidated.

The mathematical introduction now uses the source's `T=A+H` notation and
`R=TE0-E0A0=HE0`. The compression `A0=E0*TE0` and orthogonal residual
`(I-P)TE0` are identified as the Ritz/H0=0 specialization, not the general
source setup. The reader's guide now describes the actual displayed historical
**ambient** theorem (A, B, U, V, B-A); it no longer explains nonexistent M/R
binders or a directed block as though they occurred in that display.

The procedure appendix explains persisted source context, foundation modules,
agent handoffs, mechanical checks, and semantic review without inventing a
fixed model orchestration system. It retains the stated limitation that the
supervisors were not Davis--Kahan domain experts. Practitioner counts remain
the supplied data snapshot; successful data validation does not verify every
external account or make the sample representative. No new practitioner data
or independently verified prevalence estimate was added.

The supplied workflow image is preserved. Its caption qualifies "minimal
hypotheses": review compares hypotheses with the source rather than demanding
that the source itself be optimal. The figure's "often overclaim" wording is
not a measured frequency in this case study. Before final publication, replacing
it with "A checked proof may target a different statement" would avoid a
prevalence claim. No figure was redrawn and no dashboard screenshot fabricated.
The manuscript builds with an explicit omission note until the dashboard is
regenerated.

## 6. Validation and promotion instructions

Paper generation, prose checks, PDF layout checks, and static ledger validation
are run separately and recorded in `formalization_process_review_validation.md`.
The static ledger check must report 28/29 and the terminal gate must reject the
open row. No change to that gate is made to count the candidate as complete.
The small checker change admits `scope_restricted` only with blocked semantic
certification and an explicit remaining gap.

On a checkout with the pinned toolchain and dependencies:

```bash
lake build DavisKahan.Sources.DavisKahan1970.SinTwoThetaCommonDomain
lake env lean DavisKahan/Sources/DavisKahan1970/Audits/SinTwoThetaCommonDomainUsage.lean
```

Resolve any compiler errors, inspect every public type and reported axiom,
and check the common-domain and norm boundaries against the source. Only then
add imports, replace accepted aliases/evidence, close the obligation, and run
the full project gates. Do not promote it merely because the paper compiles.

## Supplied-input hashes

- `aiq-dkps-formalization-source-2026-09-09T160555-5-13ea1322d4e4.tar.gz`: `783298866ebe5444e00907ef832a3dc404147f9c391559cb93ef525dc7a2d361`
- `davis-kahan-1970-modernized-transcription(1).tex`: `4d93f47ca2d0a1fcf84bf8fc6a86bfddbeb55e7b4e17260641936602f7463ac3`
- `formalization_workflow(1).png`: `87c389e71dde2db38b55243d45f8fdf80e9583d0fc0da4e7090c75cf29e4f846`
